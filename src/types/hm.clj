(ns types.hm
  (:refer-clojure :exclude [name]))

(defprotocol Named
  (name [thing]))

(defprotocol Type
  (unify* [type other]))

(defprotocol TypeOp
  (types  [type-op])
  (mapply [type-of f]))

(declare TypeVar? TypeOp? unify)

(defrecord TypeOperator [type-name ts]
  Named
  (name [_] type-name)
  Type
  (unify* [t o]
    (cond (TypeVar? o) (unify* o t)
          (TypeOp?  o) (if (and (= type-name (name o))
                                (= (count ts) (count (types o))))
                         (->TypeOperator
                          type-name
                          (into [] (map (partial apply unify))
                            (map vector types (types o))))
                         (throw (ex-info "Unification mismatch")))
          :else            (throw (ex-info "Can't unify"))))
  TypeOp
  (types [_] types)
  (mapply [op f]
    (assoc op :types (map f types))))

(defn ->TypeOperator [name & types]
  (TypeOp. name types))

(def Int  (->TypeOperator         "Int"))
(def Bool (->TypeOperator         "Bool"))
(def Fn   (partial ->TypeOperator "Fn"))

(def TypeOp? (partial satisfies? TypeOp))

(defprotocol TypeVar
  (instantiate [type-var instance])
  (instance    [type-var])
  (generic?    [type-var non-generic]))

(def TypeVar? (partial satisfies? TypeVar))

(declare occurs?)

(defrecord TypeVariable [v inst]
  Named
  (name [_] v)
  Type
  (unify* [t other]
    (if (= t other)
      t
      (if-not (occurs? t other)
        (instantiate t other)
        (throw (ex-info "Can't recursively unify")))))

  TypeVar
  (instantiate [tv inst']
    (assoc tv :instance inst'))
  (instance [tv]
    inst)
  (generic? [tv non-generic]
    (not (contains? non-generic tv))))

(let [cur (atom (dec (int \a)))]
  (defn type-var! []
    (TypeVariable. (swap! cur inc) nil)))

(defn prune [t]
  (if-let [inst (and (TypeVar? t) (instance t))]
    (instantiate t (prune inst))
    t))

(defn occurs? [type-var type-expr]
  (let [type-expr (prune type-expr)]
    (or (= type-expr type-var)
        (and (TypeOp? type-expr)
             (contains? (types type-expr) v)))))

(defn fresh [t non-generic]
  (let [mappings (volatile! {})
        rec      (fn rec [t]
                   (let [t (prune t)]
                     (if (TypeVar? t)
                       (-> mappings
                           (cond-> (and (generic? t non-generic)
                                        (not (@mappings t))) (vswap! assoc t (type-var!)))
                           t))
                     (mapply t rec)))]
    (rec t)))

(defn type-of [name env non-generic]
  (cond (env name)      (fresh (env name) non-generic)
        (integer? name) Integer
        :else           (throw (ex-info (str "Undefined: " name))
                          {:name        name
                           :env         env
                           :non-generic non-generic})))

(defn unify [t1 t2]
  (unify* (prune t1) (prune t2)))

(defprotocol Node
  (-analyze [node env non-generic]))

(defn analyze
  ([node env non-generic] (-analyze node env non-generic))
  ([node env]             (recur node env #{})))

(defrecord Identifier [v])
(defrecord Apply      [f x])
(defrecord Lambda     [x body])
(defrecord Let        [bind val body])
(defrecord LetRec     [bind val body])

(extend-protocol Node
  java.lang.String ; identifier
  (-analyze [{v :v} env non-generic]
    (type-of v env non-generic))

  Apply
  (-analyze [{f :f x :x} env non-generic]
    (let [f-t (analyze f env non-generic)
          x-t (analyze x env non-generic)]
      (unify (Fn x-t (type-var!)) f-t)))

  Lambda
  (-analyze [{x :x body :body} env non-generic]
    (let [arg-t (type-var!)
          ret-t (analyze body (assoc env x arg-t) (conj non-generic arg-t))]
      (Fn arg-t ret-t)))

  Let
  (-analyze [{bind :bind val :val body :body} env non-generic]
    (let [val-t (analyze val env non-generic)]
      (analyze body (assoc env bind val-t) non-generic)))

  LetRec
  (-analyze [{bind :bind val :val body :body} env non-generic]
    (let [val-t  (type-var!)
          env'   (assoc env bind val-t)
          bind-t (analyze bind env' (conj non-generic val-t))]
      (analyze body (assoc env' bind (unify val-t bind-t)) non-generic)
      )))
