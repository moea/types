(ns types.optimized
  (:require [clojure.core.match :refer [match]]
            [clojure.walk :as walk])
  (:refer-clojure :exclude [type name eval apply]))


(let [current-id (atom 0)]
  (defn new-var! [level]
    (atom [:unbound (swap! current-id inc) level]))

  (defn new-generic-var! []
    (atom [:generic (swap! current-id inc)])))


(def atom? (partial instance? clojure.lang.Atom))

(defn maybe-deref [x]
  (cond-> x (atom? x) deref))

(defn adjust-levels! [type-var-id level type]
  (match type
    [:type-app type' args]
    (do
      (adjust-levels! type-var-id level type')
      (doseq [t args]
        (adjust-levels! type-var-id level t)))
    [:-> type-params ret-type]
    (do
      (doseq [t type-params]
        (adjust-levels! type-var-id level t))
      (adjust-levels! type-var-id level ret-type))
    [:const _] nil
    :else
    (do
      (println "MATCHING" type)
      (match @type
        [:link type']
        (adjust-levels! type-var-id level type')
        [:generic _]
        (assert false)
        [:unbound type-var-id' level']
        (do
          (assert (not= type-var-id type-var-id') "Recursive types")
          (when (< level level')
            (/ 1 0)
            (reset! type [:unbound type-var-id' level])))))))

(defn unify! [t o]
  (println "unify!" (maybe-deref t) (maybe-deref o))
  (if (not= t o)
    (match [t o]
      [[:const n] [:const n']]
      (assert (= n n') (str "Can't unify differing constants " n n'))

      [[:type-app type args] [:type-app type' args']]
      (do
        (unify! type type')
        (doseq [[a a'] (map vector args args')]
          (unify! a a')))

      [[:-> types ret-t] [:-> types' ret-t']]
      (do
        (doseq [[t t'] (map vector types types')]
          (unify! t t'))
        (unify! ret-t ret-t'))
      :else
      (let [t' (maybe-deref t)
            o' (maybe-deref o)]
        (match [t' o']
          [[:link type] _]
          (unify! type o)

          [_ [:link type]]
          (unify! t type)

          [[:unbound id level] _]
          (do (adjust-levels! id level o)
              (reset! t [:link o]))

          [_ [:unbound id level]]
          (do (adjust-levels! id level t)
              (reset! o [:link t]))

          :else (do
                  (println "> "t' "\n" "> " o')
                  (assert false "Cannot unify types")))))))

(defn generalize [level type]
  (match type
    [:type-app type' args]  [:type-app (generalize level type') (for [t args]
                                                                  (generalize level t))]
    [:-> params ret-t]      [:-> (for [t params]
                                   (generalize level t)) (generalize level ret-t)]
    [:const _]              type
    :else
    (match @type
      [:generic _]          type
      [:link type']         (generalize level type')
      [:unbound id level'] (if (< level level')
                             (atom [:generic id])
                             type))))

(defn instantiate [level t]
  (let [id->var (volatile! {})]
    (letfn [(f [t]
              (match t
                [:const    _] t
                [:type-app type args]    [:type-app (f type)       (map f args)]
                [:->       params ret-t] [:->       (map f params) (f ret-t)]
                :else
                (do
                  (match @t
                    [:unbound _ _] t
                    [:link    t]   (f t)
                    [:generic id]  (if-let [v (get @id->var id)]
                                     v
                                     (let [var (new-var! level)]
                                       (vswap! id->var assoc id var)
                                       var))))))]
      (f t))))


(defn match-fn-type [n-params type]
  (match type
    [:-> params ret-t]
    (do
      (assert (= (count params) n-params) "Unexpected number of arguments")
      [params ret-t])
    :else
    (match @type
      [:link type']
      (match-fn-type n-params type')
      [:unbound id level]
      (let [params (for [i (range n-params)] (new-var! level))
            ret-t  (new-var! level)]
        (/ 1 0)
        (reset! type [:link [:-> params ret-t]])
        [params ret-t]))))

(defn infer [env level expr]
  (match expr
    [:var v-name]
    (do
      (if-let [t (env v-name)]
        (instantiate level t)
        (assert false (str "Variable " v-name " not found"))))
    [:fun params body]
    (let [params->types (zipmap params (repeatedly #(new-var! level)))
          fn-env        (merge env params->types)
          ret-t         (infer fn-env level body)]
      [:-> (mapv params->types params) ret-t])
    [:let var vall body]
    (let [var-type (infer env (inc level) vall)
          gen-type (generalize level var-type)]
      (infer (assoc env var gen-type) level body))
    [:call fnn args]
    (let [[param-types ret-type] (match-fn-type (count args) (infer env level fnn))]
      (doseq [[p a] (map vector param-types args)]
        (unify! p (infer env level a)))
      ret-type)))

(defn infer-fresh [env expr]
  (infer env 0 expr))


(defn constant-lookup [t env]
  (match t
    [:const name] (env name t)
    [:type-app type args]
    (do
      [:type-app (constant-lookup type env) (for [a args]
                                              (constant-lookup a env))])
    [:-> param-types ret-t]
    [:-> (for [p param-types]
           (constant-lookup p env)) (constant-lookup ret-t env)]
    :else (do
            (assert (atom? t) (str "Not an atom: " t))
            t)
    ))

(def reserved #{:for-all :-> :const :type-app :call :var :let :fun})

(defmulti expand-rule (fn [expr env] (first expr)))

(defn make-constant [x]
  (walk/postwalk
   (fn [form]
     (if (or (and (keyword? form)
                  (not (reserved form)))
             (symbol? form))
       [:const form]
       form))
   x))

(defmethod expand-rule :for-all [[_ [& consts] body] env]
  (let [syms (map second consts)
        env  (merge env (zipmap syms (repeatedly #(new-generic-var!))))]
    (constant-lookup body env)))

(def identifier #{'lambda 'let})

(defn ->maybe-var [thing]
  (if (and (or (symbol?  thing)
               (nil?     thing)
               (boolean? thing))
           (not (identifier thing)))
    [:var thing]
    thing))

(defn convert [form]
  (match (cond-> form (list? form) vec)
    ['lambda [& args] body] [:fun args (convert body)]
    ['let    [b v]    body] [:let b (convert v) (convert body)]
    [f & args]              [:call (convert f) (mapv convert args)]
    :else
    (->maybe-var form))

  )

(let [env {'id   (expand-rule (make-constant [:for-all '[a] [:-> ['a]  'a]]) {})
           nil   (expand-rule (make-constant [:for-all '[a] [:type-app :list '[a]]]) {})
           'cons (expand-rule (make-constant [:for-all '[a] [:-> ['a [:type-app :list '[a]]] [:type-app :list '[a]]]]) {})
           'pair (expand-rule (make-constant  [:for-all '[a b] [:-> '[a b] [:type-app :pair '[a b]]]]) {})
           'first (expand-rule (make-constant [:for-all '[a b] [:-> [[:type-app :pair '[a b]]] 'a]]) {})
           'second (expand-rule (make-constant [:for-all '[a b] [:-> [[:type-app :pair '[a b]]] 'b]]) {})
           'inc     (make-constant [:-> ['int] 'int])
           'one     [:const 'int]
           true    [:const 'bool]
           'map     (expand-rule
                     (make-constant
                      [:for-all '[a b] [:-> [[:-> ['a] 'b] [:type-app :list '[a]]] [:type-app :list '[b]]]]) {})
           }]

  (infer-fresh env (convert
                    '(cons one nil)))
  )
