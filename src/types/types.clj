(ns types.types
  (:require [clojure.set :as set]
            [types.common :as c])
  (:refer-clojure :exclude [get name]))

(declare TypeVar? Fn?)

(defprotocol TypeLike
  (free [t])
  (sub  [t sub]))

(defprotocol TypeVariable
  (name [tv]))

(defprotocol Type
  (unify [t other]))

(defprotocol Scheme
  (instantiate [ts]))

(defprotocol Env
  (add  [e v scheme])
  (get* [e v])
  (generalize [e t]))

(defn join-subs [s s']
  (reduce-kv
   (fn [acc v t]
     (assoc acc v (sub t acc)))
   s s'))

(defn bind [v-name t]
  (when-not (satisfies? TypeLike t)
    (throw (ex-info "Expected type" {:value t})))
  (when ((free t) v-name)
    (throw (ex-info "Var is free" {:var v-name :type t})))
  (if (and (TypeVar? t) (= (name t) v-name))
    {}
    {v-name t}))

(defn- anon-t []
  (reify
    TypeLike
    (free [_]
      #{})
    (sub [t _]
      t)
    Type
    (unify [t o]
      (when-not (TypeVar? o)
        (throw (ex-info (str "Can't unify with " o) {:type o})))
      (unify o t))))

(def Int  (anon-t))
(def Bool (anon-t))

(defrecord Fn [l r]
  TypeLike
  (free [_]   (set/union (free l) (free r)))
  (sub  [_ e] (->Fn (sub l e) (sub r e)))
  Type
  (unify [t o]
    (cond (TypeVar? o) (unify o t)
          (Fn? o)      (let [sub'  (unify l (:l o))
                             sub'' (unify (sub r sub') (sub (:r o) sub'))]
                         (join-subs sub' sub''))
          :else
          (throw (ex-info (str "Can't unify fn w/ " (type o)) {:other o :types [t o]})))))

(def Fn? (partial instance? Fn))

(defrecord TypeVar [name]
  TypeLike
  (free [_]   #{name})
  (sub  [t e]
    (e name t))
  TypeVariable
  (name [_] name)
  Type
  (unify [_ o] (bind name o)))

(def TypeVar? (partial instance? TypeVar))

(defrecord TypeScheme [t bound]
  TypeLike
  (free [_]
    (set/difference (free t) bound))
  (sub [_ e]
    (let [e (into {}
              (for [[k v] e :when (not (bound k))]
                [k v]))]
      (->TypeScheme (sub t e) bound)))
  Scheme
  (instantiate [_]
    (sub t (into {} (for [b bound]
                      [(:name b) (->TypeVar (c/*new-type-var*))])))))

(defrecord TypeEnv [schemes]
  TypeLike
  (free [_] (reduce set/union #{} (map free (vals schemes))))
  (sub  [_ e]
    (->TypeEnv
     (into {}
       (for [[k scheme] schemes]
         [k (sub scheme e)]))))
  Env
  (get* [_ v]
    (schemes v))
  (add  [_ v scheme]
    (->TypeEnv (assoc schemes v scheme)))
  (generalize [env t]
    (let [bound (set/difference (free t) (free env))]
      (->TypeScheme t bound))))

(defn ->TypeEnv [& [env]]
  (TypeEnv. (or env {})))
