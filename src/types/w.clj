(ns types.w
  (:require [types.types  :as t]
            [types.common :as c])
  (:refer-clojure :exclude [type])
  (:gen-class))

(defmulti type (fn [v _] (first v)))

(defmethod type :expr/var [[_ name] env]
  (if-let [scheme (t/get* env name)]
    [{} (t/instantiate scheme)]
    (throw (ex-info "Unbound" {:var name :env env}))))

(defmethod type :expr/literal [[_ literal] env]
  (type literal env))

(defmethod type :expr/lambda [[_ x expr] env]
  (let [tvar     (t/->TypeVar (c/*new-type-var*))
        env      (t/add env x (t/->TypeScheme tvar #{}))
        [sub t]  (type expr env)]
    [sub (t/->Fn (t/sub tvar sub) t)]))

(defmethod type :expr/apply [[_ f x] env]
  (let [tvar        (t/->TypeVar (c/*new-type-var*))
        [sub-f t-f] (type f  env)
        [sub-x t-x] (type x (t/sub env sub-f))
        sub         (t/unify (t/sub t-f sub-x) (t/->Fn t-x tvar))
        csub        (t/join-subs sub (t/join-subs sub-x sub-f))]
    [csub (t/sub tvar sub)]))

(defmethod type :expr/let [[_ x b in] env]
  (let [[sub t]     (type b env)
        t-sub       (t/generalize (t/sub env sub) t)
        env         (t/add env x t-sub)
        t-env-sub   (t/sub env sub)
        [sub' t-in] (type in t-env-sub)]
    [(t/join-subs sub sub') t-in]))

(defn infer [expr & [env]]
  (let [env     (t/->TypeEnv env)
        [sub t] (type expr env)]
    (t/sub t sub)))

(defn -main [& _]
  (binding [c/*new-type-var* (let [i (atom (dec (int \a)))]
                               #(str (char (swap! i inc))))]
    (let [tv   (c/*new-type-var*)
          env  {"id"  (t/->TypeScheme (t/->Fn (t/->TypeVar tv) (t/->TypeVar tv)) #{tv})
                "inc" (t/->TypeScheme (t/->Fn t/Int t/Int) #{})}
          expr [:expr/lambda "x"
                [:expr/let "y" [:expr/apply [:expr/var "id"] [:expr/var "x"]]
                 [:expr/apply [:expr/var "inc"] [:expr/var "x"]]]]]
      (infer expr env))))
