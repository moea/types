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
      (if (TypeVar? o)
        (unify o t)
        {}))))

(def Int  (anon-t))
(def Bool (anon-t))

(defrecord Fn [l r]
  TypeLike
  (free [_]   (set/union (free l) (free r)))
  (sub  [_ e] (->Fn (sub l e) (sub r e)))
  Type
  (unify [t o]
    (when-not (Fn? o)
      (throw (ex-info "Can't unify fn w/" {:other o :types [t o]})))
    (join-subs (unify l (:l o)) (unify r (:r o)))))

(def Fn? (partial instance? Fn))

(defrecord TypeVar [name]
  TypeLike
  (free [_]   #{name})
  (sub  [t e] (or (e name) t))
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
    (sub t (zipmap bound (repeatedly #(->TypeVar (c/*new-type-var*)))))))

(defrecord TypeEnv [schemes]
  TypeLike
  (free [_] (reduce set/union #{} (map free (vals schemes))))
  (sub  [_ e]
    (->TypeEnv
     (into {}
       (for [[k scheme] schemes]
         [k (sub scheme e)]))))
  Env
  (get* [_ v] (schemes v))
  (add  [_ v scheme]
    (->TypeEnv (assoc schemes v scheme)))
  (generalize [env t]
    (let [bound (set/difference (free t) (free env))]
      (->TypeScheme t bound))))

(defn ->TypeEnv [& [env]]
  (TypeEnv. (or env {})))
