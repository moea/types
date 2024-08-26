(ns types.optimized
  (:require [clojure.core.match :refer [match]]
            [clojure.walk :as walk])
  (:refer-clojure :exclude [type name]))


(let [current-id (atom 0)]
  (defn new-var! []
    (atom [:unbound (swap! current-id inc)]))

  (defn new-generic! []
    (atom [:generic (swap! current-id inc)])))


(def atom? (partial instance? clojure.lang.Atom))

(defn maybe-deref [x]
  (cond-> x (atom? x) deref))

(defn unify! [t o]
  (when (not= t o)
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

          [[:unbound id] _]
          (reset! t [:link o])

          [_ [:unbound id]]
          (reset! o [:link t]))))))

(defn instantiate [t]
  (let [id->var (volatile! {})]
    (letfn [(f [t]
              (match t
                [:const    _] t
                [:type-app type args]    [:type-app (f type)       (map f args)]
                [:->       params ret-t] [:->       (map f params) (f ret-t)]
                :else
                (match @t
                  [:unbound _]  t
                  [:link    t]  (f t)
                  [:generic id] (if-let [v (get @id->var id)]
                                  v
                                  (let [var (new-var!)]
                                    (vswap! id->var assoc id var)
                                    var)))))]
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
      [:unbound id]
      (let [params (repeatedly n-params (new-var!))
            ret-t  (new-var!)]
        (reset! type [:link [:-> params ret-t]])
        [params ret-t]))))

(defn infer [env expr]
  (match expr
    [:var v-name]
    (do
      (if-let [t (env v-name)]
        (instantiate t)
        (assert false (str "Variable " v-name " not found"))))
    [:fun params body]
    (let [params->types (zipmap params (repeatedly new-var!))
          fn-env        (merge env params->types)
          ret-t         (infer fn-env body)]
      [:-> (mapv params->types params) ret-t])
    [:let var vall body]
    (let [var-type (infer env vall)]
      (infer (assoc env var var-type) body))
    [:call fnn args]
    (let [[param-types ret-type] (match-fn-type (count args) (infer env fnn))]
      (doseq [[p a] (map vector param-types args)]
        (unify! p (infer env a)))
      ret-type)))

(let [identifier? #{'lambda 'let}]
  (defn ->maybe-var [thing]
    (if (and (or (symbol?  thing)
                 (nil?     thing)
                 (boolean? thing))
             (not (identifier? thing)))
      [:var thing]
      thing)))

(defn translate [form]
  (match (cond-> form (list? form) vec)
    ['lambda [& args] body] [:fun args (translate body)]
    ['let    [b v]    body] [:let b (translate v) (translate body)]
    [f & args]              [:call (translate f) (mapv translate args)]
    :else
    (->maybe-var form)))

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
    :else
    t))

(let [identifier? #{:for-all :-> :type-app}]
  (defn ->maybe-const [x]
    (if (not (identifier? x))
      [:const x]
      x)))

(defn translate-decl [form]
  (match (cond-> form (list? form) vec)
    ['for-all [& vars] body]
    (let [env' (zipmap vars (repeatedly new-generic!))]
      (constant-lookup (translate-decl body) env'))
    ['-> [& args] ret] [:-> (mapv translate-decl args) (translate-decl ret)]
    [ctor [& args]]    [:type-app [:const (keyword ctor)] (mapv translate-decl args)]
    :else
    (->maybe-const form)))

(defn build-env [m]
  (reduce-kv
   (fn [env id decl]
     (assoc env id (translate-decl decl)))
   {}
   m))

(defn- final-prettify [form ids]
  (match form
    [:unbound id]         (do
                            (when-not (@ids id)
                              (swap! ids assoc id (symbol (str (char (+ (int \a) (count @ids)))))))
                            (clojure.walk/postwalk-replace
                             {[:unbound id] (@ids id)} form))
    [:type-app ctor args] [(symbol ctor) (mapv #(final-prettify % ids) args)]
    [:-> args ret]        (list '-> (mapv #(final-prettify % ids) args) (final-prettify ret ids))
    :else                 form))

(let [junk? (comp #{:const :link} first)]
  (defn- prettify-output [form]
    (let [form (->> form
                    (clojure.walk/prewalk #(cond-> % (atom? %) deref))
                    (clojure.walk/postwalk
                     (fn [form]
                       (let [form (if (and (vector? form) (junk? form))
                                    (subvec form 1)
                                    form)]
                         (if (and (vector? form) (= 1 (count form)))
                           (first form)
                           form)))))
          ids  (atom {})]
      (final-prettify form ids))
    ))

(let [env (build-env '{id     (for-all [a]   (-> [a] a))
                       nil    (for-all [a]   [list [a]])
                       cons   (for-all [a]   (-> [a [list [a]]] [list [a]]))
                       map    (for-all [a b] (-> [[-> [a] b] [list [a]]] [list [b]]))
                       pair   (for-all [a b] (-> [a b] [pair [a b]]))
                       first  (for-all [a b] (-> [[pair [a b]]] a))
                       second (for-all [a b] (-> [[pair [a b]]] b))
                       inc    [-> [int] int]
                       zero   int
                       succ   [-> [int] int]
                       true   bool
                       })]

  (prettify-output (infer env (translate
                               'map)))
  )
