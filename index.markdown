---
title: Algorithm W in Clojure
layout: basic
---

<h1>A Compact Algorithm W Implementation in Clojure</h1>
<div align="right">
Moe Aboulkheir<br />
moe.aboulkheir@gmail.com
</div>

Damas-Hindley-Milner / [Algorithm W](https://jeremymikkola.com/posts/2018_03_25_understanding_algorithm_w.html) implemented in Clojure using atoms.  Informed by the [OCaml GYOTS](https://github.com/tomprimozic/type-systems/tree/master/algorithm_w) implementation, though much more succint.  This is only in part because of avoiding the ranked type optimization.  I previously implemented a less mature, purely functional version of this same algorithm [here](https://github.com/moea/types/tree/main/src/types), without proper support for generics.
<br />
<br />
Type inference is about 100 lines, with about 80 more in a separate namespace to get the inputs and outputs such that they can reasonably be supplied by / read by a human.  When we're done, we'll be able to do stuff like:

```clojure
(infer
  (build-env '{cons  (for-all [a]   (-> [a [list [a]]] [list [a]]))
               map   (for-all [a b] (-> [(-> [a] b) [list [a]]] [list [b]]))
               empty (for-all [a]   [list [a]])
               t     bool
               not   (-> [bool] bool)})
  '(map
     (lambda [x]
       (lambda [y]
         (not x)))
     (cons t empty)))
;; =>
[list [(-> [a] bool)]]
;; (a list of functions taking some type and returning bool)
;; the type system doesn't know or care what bool is.
```
<br />
Note that in the type declaration DSL, the `->` is being used as a prefix typing arrow, to connect a function's parameter types to its return type, not as Clojure's thread first macro.  Similarly, none of the overlapping symbols like cons, map, empty, not, etc. have any external semantics.
<br />
<br />
I think the implementation is quite easy to follow.  The basic conceit is that we use atoms for type variables, and use a `[:link <target>]` value when we've unified a type variable, so that we can pattern match on it after dereferencing and recursively call whatever function on the contents.  In the dispatch code, `:type-app` refers to the application of a type to generic type variables, as in `[list [a]]` above.

It's most helpful if we show the frontend of the inference engine first, which translates S-expressions into tagged vectors for consumption by infer/unify.  There is a distinction between type declarations, which are mostly literals, except for the `for-all` and arrow operators (see `translate-decl`) and programs (see `translate`).

<h2>frontend.clj</h2>

```clojure
(ns types.mutable.frontend
  (:require [types.mutable.w :refer [new-generic! atom?]]
            [clojure.core.match :refer [match]]))

(let [identifier? #{'lambda 'let}]
  (defn ->maybe-var [thing]
    (if (and (symbol? thing)
             (not (identifier? thing)))
      [:var thing]
      thing)))

;; program elements are tagged vectors of :var, :fun, :let or :call

(defn translate [form]
  (match (cond-> form (list? form) vec)
    ['lambda [& args] body] [:fun args (translate body)]
    ['let    [b v]    body] [:let b (translate v) (translate body)]
    [f & args]              [:call (translate f) (mapv translate args)]
    :else (->maybe-var form)))

;; (translate '(let [x zero] ((lambda [y] (succ y)) x)))
;; =>
;; [:let
;;  x
;;  [:var zero]
;;  [:call [:fun [y] [:call [:var succ] [[:var y]]]] [[:var x]]]]

;; Now we move on to type declarations, tagged vectors of :const, :type-app, or :-> (arrow)

(defn constant-lookup [t env]
  (match t
    [:const name] (env name t)
    [:type-app type args]
    [:type-app (constant-lookup type env) (for [a args]
                                            (constant-lookup a env))]
    [:-> param-types ret-t]
    [:-> (for [p param-types]
           (constant-lookup p env)) (constant-lookup ret-t env)]
    :else t))

(let [identifier? #{:for-all :-> :type-app}]
  (defn ->maybe-const [x]
    (if (not (identifier? x))
      [:const x]
      x)))

;; Transform a vaguely human-readable type declaration into something
;; the interpreter can deal with

(defn translate-decl [form]
  (match (cond-> form (list? form) vec)
    ['for-all [& vars] body]
    (let [env (zipmap vars (repeatedly new-generic!))]
      (constant-lookup (translate-decl body) env))
    ['-> [& args] ret] [:-> (mapv translate-decl args) (translate-decl ret)]
    [ctor [& args]]    [:type-app [:const (keyword ctor)] (mapv translate-decl args)]
    :else              (->maybe-const form)))

;; (translate-decl 'bool)
;;   => [:const bool]
;; (translate-decl '(-> [int] int))
;;   => [:-> [[:const int]] [:const int]]
;; (translate-decl '(for-all [a] [list [a]]))
;;  => [:type-app [:const :list] (#<Atom@1: [:generic 1]>)]
```

We just have a few more functions in this namespace for cleaning up the output of `infer`.  They are not particularly instructive.

```clojure
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
          #(cond-> % (and (vector? %) (junk? %)) second))
         rewrite-type-vars)))
```

Similarly, here, we're going to `(declare unify!)` and put its declaration last, because it's not particularly informative, it's just some pattern-matching line-noise.

<h2>w.clj</h2>
```clojure
(ns types.mutable.w
  (:require [clojure.core.match :refer [match]])
  (:refer-clojure :exclude [type name]))

(let [current-id (atom 0)]
  (defn new-var! []
    (atom [:unbound (swap! current-id inc)]))

  (defn new-generic! []
    (atom [:generic (swap! current-id inc)])))

(def atom? (partial instance? clojure.lang.Atom))

(defn maybe-deref [x]
  (cond-> x (atom? x) deref))

;; instantiate type variables across the given term for an inference run

(defn instantiate [t]
  (let [id->var (volatile! {})]
    (letfn [(f [t]
              (match t
                [:const    _]            t
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

(declare unify! match-fn-type!)

(defn infer [env expr]
  (match expr
    [:var v-name]
    (if-let [t (env v-name)]
      (instantiate t)
      (assert false (str "Variable " v-name " not found")))
    [:fun params body]
    (let [params->types (zipmap params (repeatedly new-var!))
          fn-env        (merge env params->types)
          ret-t         (infer fn-env body)]
      [:-> (mapv params->types params) ret-t])
    [:let var vall body]
    (let [var-type (infer env vall)]
      (infer (assoc env var var-type) body))
    [:call fnn args]
    (let [[param-types ret-type] (match-fn-type! (count args) (infer env fnn))]
      (doseq [[p a] (map vector param-types args)]
        (unify! p (infer env a)))
      ret-type)))
```

Let's try
```clojure
(infer
  (build-env '{succ  (-> [int] int)
               zero int})
  (translate '(succ zero)))
;; => int
```

What happens in this case is `translate` returns `[:call [:var succ] [[:var  zero]]`. `infer` gives us the return type of `succ` after successfully unifying its single `int` parameter with the `int` zero, so we get back `int`.  Without looking at it, we can reason that unify doesn't do any work when its parameters are identical.  Now, what about that hairy clause at the end of `match-fn-type!` below this exposition?  Consider the expression `((lambda [x] (x zero)) succ)`, or `[:call [:fun [x] [:call [:var x] [[:var zero]]]] [[:var succ]]]` (which evaluates to int).  infer's destructuring clause for `:fun` is pretty simple, per above:

```clojure
[:fun params body]
(let [params->types (zipmap params (repeatedly new-var!))
      fn-env        (merge env params->types)
      ret-t         (infer fn-env body)]
  [:-> (mapv params->types params) ret-t])
```

So, for each parameter, we mint a new atom pointing at an unbound variable, stuff those into the top of the environment, and then infer the body term within that environment, returning an arrow from the parameter types to return type.  Inside the recursive infer call, x will be looked up in the env, and the dispatch code for :call will invoke match-fn-type!, whose :unbound guard will set the contents of the atom to a :link to a function of the expected number of unbound parameters to an unbound return type, so (-> [a] b) in our DSL.  Here's the offending clause, before I type too much:


```clojure
(defn match-fn-type! [n-params type]
  (match type
    [:-> params ret-t] [params ret-t]
    :else
    (match @type
      [:link type'] (match-fn-type! n-params type')
      [:unbound id]
      (let [params (repeatedly n-params new-var!)
            ret-t  (new-var!)]
        (reset! type [:link [:-> params ret-t]])
        [params ret-t]))))
```

We need to talk about unification a bit.  We can unify unbound variables with anything except for unbound variables.  So when we apply (x zero) in our lambda, we unify the single parameter of x with [:const int], the type of zero.  At this point x is (-> [int] b).  When we apply our lambda to succ, we need to unify (-> [int] b) with the type of succ, (-> [int] int).  As "b" just denotes an unbound variable, this unification is trivial.  But it needn't go as smoothly:

```clojure
(infer
  (build-env '{succ (-> [int] int)
               t    bool})
  (translate '((lambda [x] (x t)) succ)))
;; => "Can't unify differing constants..."
```

Finally, unify.

```clojure
(defn unify! [l r]
  (when (not= l r)
    (match [l r]
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
      (let [l' (maybe-deref l)
            r' (maybe-deref r)]
        (match [l' r']
          [[:link l-type] _]
          (unify! l-type r)
          [_ [:link r-type]]
          (unify! l r-type)
          [[:unbound id] _]
          (reset! l [:link r])
          [_ [:unbound id]]
          (reset! r [:link l]))))))
```

A further demonstration of obfuscation and generics:

```clojure
(infer
  (build-env '{cell   (for-all [a b] (-> [a b] [cell [a b]]))
               first  (for-all [a b] (-> [[cell [a b]]] a))
               second (for-all [a b] (-> [[cell [a b]]] b))
               empty  (for-all [a]   [list [a]])
               map    (for-all [a b] (-> [(-> [a] b) [list [a]]] [list [b]]))
               cons   (for-all [a]   (-> [a [list [a]]] [list [a]]))
               one    int
               zero   int
               t      bool})
 (translate '(let [l (cons (cell zero t) empty)]
               (map ((lambda [f] (lambda [c] (f c))) first)
                 (cons (cell one t) l)))))
;; => [list[int]]
```
