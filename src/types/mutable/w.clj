(ns types.mutable.w
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
      (assert (= n n') (str "Can't unify differing constants " n " " n'))
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
                  [:unbound _]    t
                  [:link    type] (f type)
                  [:generic id]   (if-let [v (get @id->var id)]
                                    v
                                    (let [var (new-var!)]
                                      (vswap! id->var assoc id var)
                                      var)))))]
      (f t))))


(defn match-fn-type! [n-params type]
  (match type
    [:-> params ret-t]
    (do
      (assert (= (count params) n-params) "Unexpected number of arguments")
      [params ret-t])
    :else
    (do
      (match @type
        [:link type']
        (match-fn-type! n-params type')
        [:unbound id]
        (let [params (repeatedly n-params new-var!)
              ret-t  (new-var!)]
          (reset! type [:link [:-> params ret-t]])
          [params ret-t])))))

(defn infer! [env expr]
  (match expr
    [:var v-name]
    (do
      (if-let [t (env v-name)]
        (instantiate t)
        (assert false (str "Variable " v-name " not found"))))
    [:fun params body]
    (let [params->types (zipmap params (repeatedly new-var!))
          fn-env        (merge env params->types)
          ret-t         (infer! fn-env body)]
      [:-> (mapv params->types params) ret-t])
    [:let var vall body]
    (let [var-type (infer! env vall)]
      (infer! (assoc env var var-type) body))
    [:call fnn args]
    (let [[param-types ret-type] (match-fn-type! (count args) (infer! env fnn))]
      (doseq [[p a] (map vector param-types args)]
        (unify! p (infer! env a)))
      ret-type)))
