(ns types.mutable.frontend
  (:require [types.mutable.w :refer [infer! new-generic! atom?]]
            [clojure.core.match :refer [match]]))

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

(defn- nth-var [n]
  (symbol (str (char (+ (int \a) n)))))

(defn- rewrite-type-vars [form]
  (let [ids (volatile! {})]
    (letfn [(f [form]
              (match form
                [:unbound id]
                (do
                  (when-not (@ids id)
                    (vswap! ids assoc id (nth-var (count @ids))))
                  (@ids id))
                [:type-app ctor args] [(symbol ctor) (mapv f args)]
                [:-> args ret]        (list '-> (mapv f args) (f ret))
                :else                 form))]
      (f form))))

(let [junk? (comp #{:const :link} first)]
  (defn- prettify-output [form]
    (->> form
         (clojure.walk/prewalk #(cond-> % (atom? %) deref))
         (clojure.walk/postwalk
          (fn [form]
            (if (and (vector? form) (junk? form))
              (second form)
              form)))
         rewrite-type-vars)))

(def env (build-env
          '{id     (for-all [a]   (-> [a] a))
            nil    (for-all [a]   [list [a]])
            cons   (for-all [a]   (-> [a [list [a]]] [list [a]]))
            map    (for-all [a b] (-> [(-> [a] b) [list [a]]] [list [b]]))
            map'   (for-all [a b] (-> [(-> [a] b)] (-> [[list [a]]] [list [b]])))
            pair   (for-all [a b] (-> [a b] [pair [a b]]))
            first  (for-all [a b] (-> [[pair [a b]]] a))
            second (for-all [a b] (-> [[pair [a b]]] b))
            inc    (-> [int] int)
            not    (-> [bool] bool)
            zero   int
            succ   (-> [int] int)
            true   bool}))

(do
  (defn tests [& pairs]
    (doseq [[form exp] (partition 2 pairs)]
      (let [res (prettify-output (infer! env (translate form)))]
        (assert (= res exp) (str res " != " exp)))))

  (defn throws? [f]
    (try
      (f)
      (catch AssertionError _
        true)))

  (defn negative-tests [& forms]
    (doseq [form forms]
      (assert (throws? #(infer! env (translate form))) form)))

  (tests
   '(cons zero nil)                 '[list [int]]
   '(cons true nil)                 '[list [bool]]
   '(pair zero true)                '[pair [int bool]]
   '(first  (pair zero true))       'int
   '(second (pair zero true))       'bool
   'map                             '(-> [(-> [a] b) [list [a]]] [list [b]])
   '(map inc (cons zero nil))       '[list [int]]
   '((map' not) (cons true nil))    '[list [bool]]
   '(map
     (lambda [x] (not x))
     (cons true (cons true nil)))   '[list [bool]]
   '(map
     (lambda [x]
       (lambda [y]
         (not x)))
     (cons true nil))               '[list [(-> [a] bool)]]
   '(((lambda [] succ)) zero)       'int
   '(let [x (lambda [y]
              (let [z (succ y)]
                (cons y (cons z nil))))]
      (x zero))                     '[list[int]])

  (negative-tests
   '(not zero)
   '(succ true)
   '(first (cons one nil))
   '((lambda [x] nil))
   '(cons one true)
   '(map inc (cons true nil))))
