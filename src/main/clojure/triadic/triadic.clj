(ns conexp.fca.triadic
  (:require [clojure.algo.generic.functor :refer [fmap]]
            [conexp.fca.contexts :as cxt]
            [conexp.fca.implications :as impl]
            [conexp.fca.exploration :as expl]
            [conexp.base :as base]
            [conexp.io.latex :refer [tex-escape LaTeX]]
            ))

;;; The following  example is similar to the one given in [cite conceptual exploration] by Ganter and Obiedkov.
;;; It shows the situation of public transport at the train station Bf. Wilhelmshöhe with direction to the city center in Kassel.
;;; From Bf. Wilhelmshöhe you can travel by one of four bus lines (52, 55, 100 and 500), four tram lines (1, 3, 4 and 7), one night tram (N3) and one regional tram (RT5) to the city center.
;;; These are the objects of our context.
;;; The buses and trams leave the station at different times throughout each day of the week.
;;; The attributes of our context are the aggregated the leave-times, more specifically, we have split each day in five distinct time slots: early morning from 4:00 to 7:00, working hours from 7:00 to 19:00, evening from 19:00 to 21:00, late evening from 21:00 to 24:00 and night from 0:00 to 4:00.
;;; A bus or tram has a cross the formal context if there is at least one leave-time in the time slot.
;;; Furthermore, we have split the days of the week into monday to friday, satureday and sunday as conditions.


(def objs [:1 :3 :4 :7 :N3 :RT5 :52 :55 :100 :500])
(def atts [:night :early-morning :working-hours :evening :late-evening ])

(def mo-fr (cxt/make-context-from-matrix objs atts [0 1 1 1 1
                                                    0 1 1 1 1
                                                    0 1 1 1 1
                                                    0 1 1 1 0
                                                    0 0 0 0 0
                                                    0 1 1 1 1
                                                    0 1 1 1 1
                                                    0 1 1 0 0
                                                    0 1 1 1 1
                                                    1 1 1 1 1]))

(def sa (cxt/make-context-from-matrix objs atts [0 0 1 1 1
                                                 0 1 1 1 1
                                                 0 1 1 1 1
                                                 0 0 1 0 0
                                                 1 0 0 0 0
                                                 0 1 1 1 1
                                                 0 1 1 0 0
                                                 0 0 0 0 0
                                                 0 1 1 1 1
                                                 0 0 1 1 1]))

(def so (cxt/make-context-from-matrix objs atts [0 0 1 1 1
                                                 0 1 1 1 1
                                                 0 1 1 1 1
                                                 0 0 0 0 0
                                                 1 0 0 0 0
                                                 0 0 1 1 1
                                                 0 0 0 0 0
                                                 0 0 0 0 0
                                                 0 1 1 1 1
                                                 0 0 1 1 1]))


(defn subposition-context-coll [cxts]
  (reduce cxt/context-subposition cxts))

(defn all-conditional-implication-theories [cond-cxt-coll] 
  (for [subset (clojure.math.combinatorics/subsets cond-cxt-coll)
        :when (not (empty? subset))]
    {:intent subset
     :extent (impl/canonical-base (subposition-context-coll subset))}))

(def cxts [mo-fr sa so])

(def cxt-family {:Mo-Fr mo-fr
                 :Sat sa
                 :Sun so})

(def cxt-family-from-book {:mo-fr (cxt/make-context-from-matrix [1 6 7 8]
                                                                [:very-early
                                                                 :working-hours
                                                                 :evening
                                                                 :late-night]
                                                                [0 1 1 1
                                                                 1 1 0 0
                                                                 1 1 1 1
                                                                 1 0 1 1])
                           :sat (cxt/make-context-from-matrix [1 6 7 8]
                                                                [:very-early
                                                                 :working-hours
                                                                 :evening
                                                                 :late-night]
                                                                [1 0 0 1
                                                                 0 0 0 0
                                                                 1 1 0 1
                                                                 1 1 1 1])
                           :sun (cxt/make-context-from-matrix [1 6 7 8]
                                                                [:very-early
                                                                 :working-hours
                                                                 :evening
                                                                 :late-night]
                                                                [0 0 1 0
                                                                 0 0 0 0
                                                                 1 1 0 1
                                                                 0 1 1 0])})


(def cxt-family2 {:A (cxt/make-context [1] [:a :b :c] [[1 :a] [1 :c]])
                  :B (cxt/make-context [1] [:a :b :c] [])})

(def cxt-family3 {:A (cxt/make-context [1] [:a :b :c] [[1 :a] [1 :c]])
                  :B (cxt/make-context [1] [:a :b :c] [[1 :c]])})

(def cxt-family4 {:A (cxt/make-context [1] [:a :b :c] [[1 :a] [1 :c]])
                  :B (cxt/make-context [1] [:a :b :c] [[1 :b] [1 :c]])})

(def cxt-family5 {:A (cxt/make-context [1 2] [:a :b :c] [[1 :a] [1 :c] [2 :a]])
                  :B (cxt/make-context [1 2] [:a :b :c] [[1 :c] [2 :a]])
                  :C (cxt/make-context [1 2] [:a :b :c] [[1 :b] [1 :c]])})

(def cxt-family6 {:A (cxt/make-context [1] [:a :b ] [[1 :a]])
                  :B (cxt/make-context [1] [:a :b ] [])})



;;; triadic context: A quadrupel (G,M,B,Y) of objects G, attributes M, conditions B, and an incidence relation Y\subseteq G \times M \times B where [g m b]\in Y reads as "the object g has the attribute m under the condition b".
(defn triadic-context->context-family
  "transform a triadic context (G,M,B,Y) into a family of contexts.  The triadic context is sliced into one formal context per condition, i.e., contexts K^c (G,M,I^c), c\\in B where (g,m)\\in I^c \\Leftrightarrow (g,m,c)\\in Y.  The function returns a map {:c K^c ...} mapping the conditions to their respective contexts.  The triadic context must be represented as a map with keys :objects :attributes :conditions and :incidence, otherwise an error is thrown."
  [triadic-context]
  (if (and (contains? triadic-context :objects)
           (contains? triadic-context :attributes)
           (contains? triadic-context :conditions)
           (contains? triadic-context :incidence))
    (let [objects (:objects triadic-context)
          attributes (:attributes triadic-context)
          incidences-by-condition (group-by #(nth % 2) (:incidence triadic-context))]
      (into {}
            (for [c (:conditions triadic-context)]
              [c (cxt/make-context objects attributes (map drop-last (c incidences-by-condition)))])
            #_(for [[condition incidences] incidences-by-condition]
                [condition (cxt/make-context objects attributes (map drop-last incidences))])))
    (throw (Throwable. "triadic context is not a map with keys :objects :attributes :conditions and :incidence"))
    ))

(defn is-context-family-triadic?
  "tests if the contexts in a context family {:cond1 cxt1 :cond2 cxt2 ...} form a triadic context, i.e., have the same sets of objects and attributes"
  [context-family]
  (let[[first-key & rest-keys :as conds] (keys context-family)
       first-context (first-key context-family)
       objs (cxt/objects first-context)
       atts (cxt/attributes first-context)]
    (->> rest-keys
         (map #(% context-family))
         (map (fn [cxt] (and
                         (= (cxt/objects cxt) objs)
                         (= (cxt/attributes cxt) atts))))
         (reduce #(every? identity [%1 %2])))))

;;; context family: A context family is a map of conditions and their context on the same set of attributes, i.e., a map {:cond1 (G1,M,I1) :cond2 (G2,M,I2) ...}
(defn context-family->triadic-context
  "transforms a context family into a triadic context.  The contexts in the family must have the same object and attribute sets otherwise an error is thrown"
  [cxt-family]
  (if (is-context-family-triadic? cxt-family)
    (let [conditions (keys cxt-family)
          objects (cxt/objects ((first conditions) cxt-family))
          attributes (cxt/attributes ((first conditions) cxt-family))
          incidence (reduce into #{} (for [c conditions]
                                       (map #(conj % c) (cxt/incidence-relation (c cxt-family)))))]
      {:objects objects
       :attributes attributes
       :conditions conditions
       :incidence incidence})
    (throw (Throwable. "context-family is not triadic"))))


(defn all-conditional-implication-theory
  "computes the canonical base of the subposition of all contexts in the family, thus computing the implications that hold under all conditions (= contexts in the family)"
  [cxt-family]
  {:intent (keys cxt-family)
   :extent (impl/canonical-base (subposition-context-coll (vals cxt-family))
                                )})

(defn all-single-condition-implication-theories
  "computes the canonical base for each context in the context-family.
  Returns a map {:condition1 canonical-base1 ..}"
  [context-family]
  (into {} (for [condition (keys context-family)]
             {condition (into [] (impl/canonical-base (condition context-family)))})))

(defn all-intersection-implication-theories
  "computes all intersections of implication theories of the contexts in a context family"
  [context-family]
  (let [impl-families (all-single-condition-implication-theories context-family)
        atts (cxt/attributes ((first (keys context-family)) context-family))
        intersect (fn [cxt-fam]  (apply (partial
                                         impl/intersect-implicational-theories
                                         atts) (vals cxt-fam)))
        subsets (filter (comp not empty?)
                        (map #(into #{} %)(clojure.math.combinatorics/subsets (keys context-family))))
        ]
    (into {}
          (for [s subsets] {s (intersect (select-keys impl-families s))}))))


(defn expert
  "creates an expert for a context that answers questions with either true or a context containing the first counterexample (by name) known to the expert.
  Input: formal context
  Output: function that takes an implication and outputs true if it holds and a counterexample if it does not hold"
   [cxt]
    (fn [question]
      (let [premise (impl/premise question)
            conclusion (impl/conclusion question)
            att-deriv (fn [atts] (set (cxt/attribute-derivation cxt atts)))
            att-closure (fn [atts]
                          (set
                           (cxt/object-derivation
                            cxt
                            (cxt/attribute-derivation cxt atts))))]
        (if (clojure.set/subset? (set conclusion) (att-closure premise))
          true
          (cxt/make-context #{(first (sort (clojure.set/difference
                                           (att-deriv premise)
                                           (att-deriv conclusion))))}
                            (cxt/attributes cxt)
                            (cxt/incidence cxt))))))

(defn cxt-map->yes-no [question [k v]]
  {k ((expert v) question)})

(defn context-union
  "compute (G_1 u G_2, M, I_1 u I_2) for contexts (G_1,M,I_1) and (G_2,M,I_2)"
  [cxt1 cxt2]
  (let [objs (clojure.set/union (set (cxt/objects cxt1))
                                (set (cxt/objects cxt2)))
        atts (clojure.set/union (set (cxt/attributes cxt1))
                                (set (cxt/attributes cxt2)))
        incidence (clojure.set/union (set (cxt/incidence-relation cxt1))
                                     (set (cxt/incidence-relation cxt2)))]
    (cxt/make-context objs atts incidence)))


(defn merge-cxt-fams [fam1 fam2]
  (into {} (for [k (keys fam1)]
             (if (some? (k fam2))
               {k (context-union (k fam1) (k fam2))}
               {k (k fam1)}))))


(defn explore-context-family
  "cxt-fam: family of contexts {:cxt-name cxt1 :cxt-name2 cxt2 ...} is the expert knowledge of the domain
  example-fam: family of contexts {:cxt-name cxt1 ...} is the family of known example knowledge under each condition - the keys must be a subset of the keys of cxt-fam"
  ([expert-cxt-fam] (explore-context-family expert-cxt-fam {} #{}))
  ([expert-cxt-fam example-fam background-impls]
   (let [cxt-fam expert-cxt-fam
         atts (cxt/attributes (first (vals cxt-fam)))
         conds (keys cxt-fam)]
     (loop [C (cxt/make-context [] conds [])
            L background-impls
            last (impl/close-under-implications L #{})
            counterexample-cxt-fam (into (zipmap (keys cxt-fam) ;construct empty contexts for all conditions
                                                 (repeat (cxt/make-context [] atts [])))
                                         example-fam)]
       (if (not last)                    ; is true if next-closed set returns nil (see conexp.base/next-closed-set for details)
         {:C C
          :L (clojure.set/difference L background-impls)
          :ex-cxt-fam counterexample-cxt-fam}
         (let [cxt (subposition-context-coll (vals counterexample-cxt-fam))
               ;; debug help
               #_(do 
                   (nl 4)
                   (println :prem last)
                   (println :sa (cxt/context-attribute-closure (:sa counterexample-cxt-fam) last))
                   (println :so (cxt/context-attribute-closure (:so counterexample-cxt-fam) last))
                   (println :sa+so (cxt/context-attribute-closure cxt last))
                   (nl 4))
               conclusion-from-last (cxt/context-attribute-closure cxt last)]
           (if (= last conclusion-from-last)
             (recur C
                    L
                    (base/next-closed-set
                     atts
                     (impl/clop-by-implications L)
                     last)
                    counterexample-cxt-fam
                    )
             (let [new-prem last
                   new-conc conclusion-from-last
                   new-impl
                   (impl/make-implication new-prem new-conc)
                   expert-answers
                   (into {} (map #(cxt-map->yes-no new-impl %) cxt-fam))
                   ;; todo fix this - you cannot simply split the implication into single attribute conclusion implications - this breaks if the implication is rejected and may lead to wrong results.
                   ;; current fix: work with the whole implication again and accept that the context C does not only contain implications with single attribute conclusions.
                   #_add-C-incidence
                    #_(for [m (clojure.set/difference new-conc new-prem)
                         k (keys expert-answers)
                         :when (true? (k expert-answers))]
                     [(impl/make-implication new-prem #{m}) k])
                   #_add-C-objs #_(for [m (clojure.set/difference new-conc
                                                              new-prem)]
                                (impl/make-implication new-prem #{m}))
                   ;; fix: see below
                   add-C-incidence                  
                    (for [k (keys expert-answers)
                         :when (true? (k expert-answers))]
                      [new-impl k])
                   add-C-objs #{new-impl}
                   
                   new-C (context-union C
                                        (cxt/make-context
                                         add-C-objs
                                         conds
                                         add-C-incidence))
                   counterexample-fam
                   (->> expert-answers
                        (filter (fn [[k v]] ((comp not true?) v)))
                        (into {})
                        ((fn [hmap] (if (every? true? (vals hmap))
                                      nil
                                      (merge-cxt-fams
                                       counterexample-cxt-fam
                                       hmap)))))
                   ;; debug help
                   #_(do
                       (nl 4)
                       (println :answers expert-answers)
                       (nl 1)
                       (println :implication new-impl)
                       (nl 1)
                       (println :counterex counterexample-fam))]
               (cond
                 counterexample-fam      ;found counterexample
                 (recur new-C               
                        L
                        last
                        counterexample-fam
                        )
                 true                    ;add implication to L
                 (recur new-C                
                        (conj L new-impl)
                        (base/next-closed-set
                         atts
                         (impl/clop-by-implications (conj L new-impl))
                         last)
                        counterexample-cxt-fam)
                 )))))))))


(defn next-extent [cxt objs]
  (base/next-closed-set (cxt/objects cxt)
                        (fn [A] (cxt/context-object-closure cxt A))
                        objs))

(defn next-intent [cxt atts]
  (base/next-closed-set (cxt/attributes cxt)
                        (fn [A] (cxt/context-attribute-closure cxt A))
                        atts))

(defn nl
  ([] (print "\n"))
  ([n] (print (clojure.string/join (repeat n "\n")))))


(defn explore-conditional-implications
  "explore conditional implications of a context family. start with exploring the all-conditional implications. then use the accepted/rejected implications, i.e. the context of conditional implications that hold under some attributes C, to generate the next set of conditions to be explored.
  note: currently this has some problems and does not explore all subsets, this is due to the nature of generating the questions based on what could hold under all conditions which disregards some potentially differentiating questions and leads to a sparser context C"
  [context-family]
  (let [cxt-fam context-family
        conds (keys context-family)
        res-all-conditional (explore-context-family cxt-fam)]
    (loop [last-C (:C res-all-conditional)
           last-L (:L res-all-conditional)
           last-ex-fam (:ex-cxt-fam res-all-conditional)
           last-C-extent (next-extent last-C #{})
           all-results [{:C last-C
                         :L last-L
                         :ex-fam last-ex-fam
                         :C-extent last-C-extent}]]
      (let [next-C-extent (next-extent last-C last-C-extent)
            intent (cxt/object-derivation last-C next-C-extent)
            ]
        (if (empty? intent)
          {:C last-C
           :examples last-ex-fam}
          #_all-results 
          (let [this-cxt-fam (select-keys cxt-fam intent)
                this-ex-fam (select-keys last-ex-fam intent)
                exploration-result (explore-context-family this-cxt-fam
                                                           this-ex-fam
                                                           next-C-extent)
                next-C (context-union last-C (:C exploration-result))
                next-L (:L exploration-result)
                next-ex-fam (merge-cxt-fams
                             last-ex-fam
                             (:ex-cxt-fam exploration-result))]
            (recur next-C
                   next-L
                   next-ex-fam
                   next-C-extent
                   (into all-results
                         {:C next-C
                          :L next-L
                          :ex-fam next-ex-fam
                          :C-extent next-C-extent
                          :C-intent intent}))))))))


(defn explore-conditional-implications-v1
  ""
  [context-family]
  (let [cxt-fam context-family
        all-conditions (into #{} (keys context-family))
        res-all-conditional (explore-context-family cxt-fam)]
    (loop [last-C (:C res-all-conditional)
           last-L (:L res-all-conditional)
           last-ex-fam (:ex-cxt-fam res-all-conditional)
           last-C-extent (next-extent last-C #{})
           all-results [{:C last-C
                         :L last-L
                         :ex-fam last-ex-fam
                         :C-extent last-C-extent}]]
      (let [next-C-extent (next-extent last-C last-C-extent)
            intent (cxt/object-derivation last-C next-C-extent)
            conditions intent]
        (if (empty? intent)
          {:C last-C
           :examples last-ex-fam}
          #_all-results 
          (let [this-cxt-fam (select-keys cxt-fam intent)
                this-ex-fam (select-keys last-ex-fam intent)
                exploration-result (explore-context-family this-cxt-fam
                                                           this-ex-fam
                                                           next-C-extent)
                next-C (context-union last-C (:C exploration-result))
                next-L (:L exploration-result)
                next-ex-fam (merge-cxt-fams
                             last-ex-fam
                             (:ex-cxt-fam exploration-result))
                ;; for each implication newly added to C we ask if they hold under all conditions not used for the current exploration and update the incidences of C accordingly
                possible-impls (cxt/objects (:C exploration-result))
                conds-to-test (clojure.set/difference all-conditions conditions)
                incidences-to-add (for [c conds-to-test
                      i possible-impls :when (true? ((expert (c context-family)) i))]
                                    [i c])
                next-C (if (not (empty? incidences-to-add))
                         (cxt/make-context (cxt/objects next-C)
                                           (cxt/attributes next-C)
                                           (concat incidences-to-add
                                                   (cxt/incidence-relation next-C)))
                         next-C)
                ]
            (recur next-C
                   next-L
                   next-ex-fam
                   next-C-extent
                   (into all-results
                         {:C next-C
                          :L next-L
                          :ex-fam next-ex-fam
                          :C-extent next-C-extent
                          :C-intent intent}))))))))

(defn add-incidences-to-context
  [cxt incidences]
  (cxt/make-context (cxt/objects cxt)
                    (cxt/attributes cxt)
                    (concat incidences
                            (cxt/incidence-relation cxt))))

(defn explore-conditional-implications-v2
  [context-family]
  (let [cxt-fam context-family
        all-conditions (into #{} (keys context-family))
        res-all-conditional (explore-context-family cxt-fam)]
    (loop [last-C (:C res-all-conditional)  ; formal context
           last-L (:L res-all-conditional)  ; set of implications
           last-ex-fam (:ex-cxt-fam res-all-conditional)  ; context family of examples given so far
           last-C-extent (next-extent last-C #{})  ; the extent for which the implication system was explored
           last-possible-C-incidences #{} ; the context C where not answered implications under conditions are true, such that we can look for the next extent in the context of true or possibly true implications
           all-results [{:C last-C
                         :L last-L
                         :ex-fam last-ex-fam
                         :C-extent last-C-extent}] ; collecting the results
           ]
      (let [next-C-extent (next-extent last-C last-C-extent)
            next-C-extent (next-extent (add-incidences-to-context last-C
                                                                  last-possible-C-incidences)
                                       last-C-extent)
            intent (cxt/object-derivation last-C next-C-extent)
            conditions intent]
        (if (empty? intent)
          {:C last-C
           :examples last-ex-fam}
          #_all-results 
          (let [this-cxt-fam (select-keys cxt-fam conditions)
                this-ex-fam (select-keys last-ex-fam conditions)
                exploration-result (explore-context-family this-cxt-fam
                                                           this-ex-fam
                                                           next-C-extent)
                next-C (context-union last-C (:C exploration-result))                
                next-L (:L exploration-result)
                next-ex-fam (merge-cxt-fams
                             last-ex-fam
                             (:ex-cxt-fam exploration-result))

                possible-impls (cxt/objects (:C exploration-result))
                conds-to-test (clojure.set/difference all-conditions conditions)
                ;; now: test each implication for each of the conditions
                ;; a) if they follow from previously accepted implications
                ;; b) if they are rejected by a previously given counterexample
                follows-from-known-implications (fn [[impl condition]]
                                                  (impl/follows? impl
                                                                 (cxt/attribute-derivation
                                                                  (condition next-C)
                                                                  #{condition})))
                rejected-by-known-examples (fn [[impl condition]] (impl/holds? impl (condition next-ex-fam)))
                possible-C-incidences-from-exploration (into #{} (for [c conds-to-test
                                                                       i possible-impls]
                                                                   [i c]))
                non-rejected-implications
                (->> (clojure.set/union
                      last-possible-C-incidences
                      possible-C-incidences-from-exploration)
                     (filter rejected-by-known-examples))
                {implications-that-follow-from-C true
                 implications-that-dont-follow false} (group-by
                                                       follows-from-known-implications
                                                       non-rejected-implications)
                next-possible-C-incidences implications-that-dont-follow
                next-C (if (not (empty? implications-that-follow-from-C))
                         (cxt/make-context (cxt/objects next-C)
                                           (cxt/attributes next-C)
                                           (concat implications-that-follow-from-C
                                                   (cxt/incidence-relation next-C)))
                         next-C)
                ]
            (recur next-C
                   next-L
                   next-ex-fam
                   next-C-extent
                   next-possible-C-incidences
                   (into all-results
                         {:C next-C
                          :L next-L
                          :ex-fam next-ex-fam
                          :C-extent next-C-extent
                          :C-intent intent}))))))))

;;; this works as expected and generates the whole lattice of implications that hold under conditions
(defn explore-conditional-implications-v3
  "explore conditional implications; before returning, explore each condition separately"
  [context-family]
  (let [cxt-fam context-family
        conds (keys context-family)
        res-all-conditional (explore-context-family cxt-fam)]
    (loop [last-C (:C res-all-conditional)
           last-L (:L res-all-conditional)
           last-ex-fam (:ex-cxt-fam res-all-conditional)
           last-C-extent (next-extent last-C #{})
           all-results [{:C last-C
                         :L last-L
                         :ex-fam last-ex-fam
                         :C-extent last-C-extent}]]
      (let [next-C-extent (next-extent last-C last-C-extent)
            intent (cxt/object-derivation last-C next-C-extent)
            ]
        (if (empty? intent)
          ;; before returning explore each condition separately (because the algorithm may have missed some differentiating questions)
          (let [single-condition-explorations
                (for [c conds]
                  (explore-context-family (select-keys context-family #{c})
                                          (select-keys last-ex-fam #{c})
                                           (cxt/attribute-derivation last-C #{c})))
                last-C (reduce context-union last-C (map :C single-condition-explorations))
                last-ex-fam (reduce merge-cxt-fams last-ex-fam (map :ex-cxt-fam single-condition-explorations))]
            {:C last-C
             :examples last-ex-fam})
          #_all-results 
          (let [this-cxt-fam (select-keys cxt-fam intent)
                this-ex-fam (select-keys last-ex-fam intent)
                exploration-result (explore-context-family this-cxt-fam
                                                           this-ex-fam
                                                           next-C-extent)
                next-C (context-union last-C (:C exploration-result))
                next-L (:L exploration-result)
                next-ex-fam (merge-cxt-fams
                             last-ex-fam
                             (:ex-cxt-fam exploration-result))]
            (recur next-C
                   next-L
                   next-ex-fam
                   next-C-extent
                   (into all-results
                         {:C next-C
                          :L next-L
                          :ex-fam next-ex-fam
                          :C-extent next-C-extent
                          :C-intent intent}))))))))


(defn context-family->context-of-conditional-implications
  "create the context of implications that hold under conditions from the context family.
  The context C = (G,M,I) has implications with one attribute conclusions as objects and the conditions as attributes. An object g (= an implication) has an attribute (= a condition) if the implication holds in the context of the condition"
  [cxt-family]
  (let [conditions (keys cxt-family)
        cxt-family-canonical-bases (into {} (map (fn [[k v]] [k (impl/canonical-base v)]) cxt-family))
        attributes (into [] (cxt/attributes ((first conditions) cxt-family)))
        objects (for [p (map (partial into #{}) (clojure.math.combinatorics/subsets attributes))
                      c attributes :when (not (clojure.set/subset? #{c} p))] (impl/make-implication p #{c}))
        incidence (for [g objects
                        c conditions
                        :when (impl/follows? g (c cxt-family-canonical-bases))]
                    [g c])]
    (cxt/make-context objects conditions incidence)))

(defn explore-conditional-implications-v4
  "explore conditional implications; use examples to generate satisfiable implications - appears NOT to work"
  [context-family]
  (let [cxt-fam context-family
        conds (keys context-family)
        res-all-conditional (explore-context-family cxt-fam)]
    (loop [last-C (:C res-all-conditional)
           last-L {conds (:L res-all-conditional)}
           last-ex-fam (:ex-cxt-fam res-all-conditional)
           last-C-extent #{} #_(next-extent last-C #{})
           all-results [{:C last-C
                         :L last-L
                         :ex-fam last-ex-fam
                         :C-extent last-C-extent}]]
      (let [possible-C (context-family->context-of-conditional-implications last-ex-fam)
            next-C-extent (next-extent possible-C last-C-extent)
            intent (cxt/object-derivation possible-C next-C-extent)
            valid-impls-for-intent (cxt/attribute-derivation last-C intent)
            ]
        (if (empty? intent)
          {:C last-C
           :examples last-ex-fam
           :L last-L}
          #_all-results 
          (let [this-cxt-fam (select-keys cxt-fam intent)
                this-ex-fam (select-keys last-ex-fam intent)
                exploration-result (explore-context-family this-cxt-fam
                                                           this-ex-fam
                                                           valid-impls-for-intent)
                next-C (context-union last-C (:C exploration-result))
                next-L (into last-L {intent (:L exploration-result)})
                next-ex-fam (merge-cxt-fams
                             last-ex-fam
                             (:ex-cxt-fam exploration-result))]
            (recur next-C
                   next-L
                   next-ex-fam
                   next-C-extent
                   (into all-results
                         {:C next-C
                          :L next-L
                          :ex-fam next-ex-fam
                          :C-extent next-C-extent
                          :C-intent intent}))))))))

(defn implication-theories-from-C
  [C]
  (for [[extent intent] (cxt/concepts C)]
    [(impl/canonical-base-from-base extent) intent]))

#_(implication-theories-from-C (:C (explore-conditional-implications-v3 cxt-family)))



;;; as presented in the paper

(defn contradicts?
  "takes an object, a context and an implication, returns true if the object is a counterexample to the implication in the context"
  [o impl cxt]
  (if (impl/holds? impl (cxt/make-context #{o}
                                           (cxt/attributes cxt)
                                           (cxt/incidence-relation cxt)))
    false
    true))

(defn counterexample
  "takes a formal context and an implication and 
  returns an counterexample with all its incidences if it exists or nil"
  [context implication]
  (let [objs (cxt/objects context)
        prem (impl/premise implication)
        concl (impl/conclusion implication)]
    (loop [o (first objs)
           other (rest objs)]
      (if (contradicts? o implication context)
        [o (into #{} (for [a (cxt/object-derivation context #{o})]
                       [o a]))]
        (if (empty? other)
          nil
          (recur (first other)
                 (rest other)))))))

(defn triadic-object-incidences
  "takes a triadic context and an object and returns all incidences of that object"
  [triadic-context object]
  (->> (:incidence triadic-context)
       (filter (fn [i] (= object (first i))))
       (into #{})))

(defn triadic-expert-from-triadic-context
  [tcxt]
  (fn [D question]
    (let [context-family (triadic-context->context-family tcxt)
          ;; test if question holds in all contexts in D
          ;; if not respond with a counterexample
          counterex-condition (->> D
                                   (map #(hash-map % (% context-family)) ,,,)
                                   (into {} ,,,)
                                   (fmap #(impl/holds? question %) ,,,)
                                   (filter (fn [[k v]] (false? v)) ,,,)
                                   (into {} ,,,)
                                   (ffirst)
                                   #_((fn [d] (counterexample (d context-family) question))))]
      (if (some? counterex-condition)
        (->> (counterexample (counterex-condition context-family) question)
             (first)
             (triadic-object-incidences tcxt)
             ((fn [coll] (vector (ffirst coll) coll))))  ;make the counterexample [g triadic-incidence]
        true))))

(defn triadic-context+conditions->subposition-context
  [triadic-context D]
  (subposition-context-coll (vals (select-keys (triadic-context->context-family triadic-context) D))))

(defn next-closure-by-implications
  [A M L]
  (base/next-closed-set
   M
   (impl/clop-by-implications L)
   A))

(defn add-counterexample-to-triadic-context
  "the counterexample [g incidence] consists of the object g and its incidence"
  [triadic-context counterexample]
  (-> triadic-context
      (update-in [:objects] conj (first counterexample))
      (update-in [:incidence] into (second counterexample))))

(defn explore-conditions
  "
  triadic-expert = the expert answering the questions
  D = the set of conditions to explore
  E = a triadic context of examples (possibly empty)
  L0 = a set of background implications known to hold for all conditions in D
  "
  [triadic-expert D E L0]
  (let [M (:attributes E)]
    (loop [A #{}
           L L0
           E E]
      (if (not A)
        [L E]
        (let [S (triadic-context+conditions->subposition-context E D)
              AJJ (cxt/context-attribute-closure S A)
              question (impl/make-implication A AJJ)]
          (if (= A AJJ)
            (recur (next-closure-by-implications A M (conj L question))
                   L
                   E)
            (let [answer (triadic-expert D question)]
              (if (true? answer)              ;no counterexample
                (recur (next-closure-by-implications A M (conj L question))
                       (conj L question)
                       E)
                (recur A
                       L
                       (add-counterexample-to-triadic-context E answer))))
          ))))))

(defn add-row-to-context
  [context [object incidence]]
  (cxt/make-context (conj (cxt/objects context) object)
                    (cxt/attributes context)
                    (into (cxt/incidence-relation context) incidence)))

(defn explore-conditions-with-C
  "
  triadic-expert = the expert answering the questions
  D = the set of conditions to explore
  E = a triadic context of examples (possibly empty)
  L0 = a set of background implications known to hold for all conditions in D
  "
  [triadic-expert D E L0]
  (let [M (:attributes E)
        B (:conditions E)
        C0 (cxt/make-context #{}
                             B
                             #{})]
    (loop [A #{}
           L L0
           E E
           C C0]
      (if (not A)
        [L C E]
        (let [S (triadic-context+conditions->subposition-context E D)
              AJJ (cxt/context-attribute-closure S A)
              question (impl/make-implication A AJJ)]
          (if (= A AJJ)
            (recur (next-closure-by-implications A M (conj L question))
                   qL
                   E
                   C)
            (let [answer (triadic-expert D question)
                  _ (println D "\t" (if (true? answer) true (first answer)) "\t" question)
                  Cnew (if (true? answer)
                         (add-row-to-context C [question (for [d D] [question d])])
                         C)]
              (if (true? answer)              ;no counterexample
                (recur (next-closure-by-implications A M (conj L question))
                       (conj L question)
                       E
                       Cnew)
                (recur A
                       L
                       (add-counterexample-to-triadic-context E answer)
                       Cnew)))))))))

(defn explore-all-conditional-theories
  "takes a triadic context of examples E
  and a context of implications known to hold C"
  [triadic-expert E C]
  (let [conditions (:conditions E)
        condition-sets (->> (clojure.math.combinatorics/subsets conditions)
                            (map #(into #{} %))
                            (filter (comp not empty?))
                            (sort-by count)
                            (reverse))]
    (loop [D (first condition-sets)
           other (rest condition-sets)
           E E
           C C]
      (if (nil? D)
        [C E]
        (let [L (cxt/attribute-derivation C D)
              [LD CD ED] (explore-conditions-with-C triadic-expert D E L)]
          (recur (first other)
                 (rest other)
                 ED
                 (context-union C CD)))))))


;;; ;;;
;;; TRIADIC EXPLORATION EXAMPLE
;;; ;;;


(def triadic-context (context-family->triadic-context cxt-family))
(def triadic-expert (triadic-expert-from-triadic-context triadic-context))
(defn empty-triadic-context-from-triadic-context [tcxt] {:objects #{}
                                                         :attributes (:attributes tcxt)
                                                         :conditions (:conditions tcxt)
                                                         :incidence #{}})
(def triadic-context-no-objects {:objects #{}
                                 :attributes (:attributes triadic-context)
                                 :conditions (:conditions triadic-context)
                                 :incidence #{}})

(defn empty-implications-context-from-triadic-context [tcxt] (cxt/make-context #{} (:conditions tcxt) #{}))
(def implications-context (empty-implications-context triadic-context))


;;; ;;;
;;; LATEX OUTPUT FUNCTIONS 
;;; ;;;

(defn cxt-family->latex [cxt-fam file]
  (spit file
        (str #_"\\begin{figure}\n\\centering\n"
             (clojure.string/join ""  (for [[cond cxt] cxt-fam]
                                        (conexp.io.latex/latex ((fn [cxt] (cxt/make-context
                                                                           (map name (cxt/objects cxt))
                                                                           (map name (cxt/attributes cxt))
                                                                           (map #(vector (name (first %)) (name (second %))) (cxt/incidence cxt)))) cxt)
                                                               :fca
                                                               (name cond)
                                                               ["early-morning"
                                                                "working-hours"
                                                                "evening"
                                                                "late-evening"
                                                                "night"])))
             #_"\\caption{}\n\\end{figure}")))


(defn implication->latexfriendly
  [impl]
  (let [premise (impl/premise impl)
        conclusion (impl/conclusion impl)]
    (str (mapv name premise) "->" (mapv name conclusion))))


(defn implcxt->latex
  [cxt file attributeorder]
  (spit file
        (str (conexp.io.latex/latex ((fn [cxt] (cxt/make-context
                                                (map implication->latexfriendly (cxt/objects cxt))
                                                (map name (cxt/attributes cxt))
                                                (map #(vector (implication->latexfriendly (first %)) (name (second %))) (cxt/incidence cxt)))) cxt)
                                    :fca
                                    " "
                                    (map name attributeorder)))))

(defn triadic-context->tikz-picture [triadic-cxt]
  (let [atts [:early-morning :working-hours :evening :late-evening :night] #_(:attributes triadic-cxt)
        objs (sort-by (juxt (comp count name) (comp first name)) (:objects triadic-cxt))
        conds (reverse (:conditions triadic-cxt))
        inci (:incidence triadic-cxt)]
    
    (with-out-str
      (println "\\begin{tikzpicture}[ matrixstyle/.style={matrix of math nodes,
               nodes in empty cells, anchor=north east, fill=white,opacity=0.7}]")
      (loop [lastc (first conds)
             c (first conds)
             rest-conds (rest conds)]
        (if (= c lastc)
          (println (str "\\matrix (" (name c) ") [draw,matrixstyle]{") )
          (println (str "\\matrix (" (name c) ") [draw,matrixstyle] at ($(" (name lastc) ".north east) - (1,1)$){") )
          )
        (doseq [o objs]
          (doseq [a atts]
            (if (contains? inci [o a c])
              (print "\\times")
              (print "\\phantom{\\times}"))
            (if (not (= a (last atts)))
              (print " & ")))
          (print "\\\\")
          (println)
          )
        (print "};")
        (if (some? (first rest-conds))
          (recur c
                 (first rest-conds)
                 (rest rest-conds)))
        )
      (println (str "\\draw[dotted] (" (name (first conds)) ".north west) -- (" (name (last conds)) ".north west);"))
      (println (str "\\draw[dotted] (" (name (first conds)) ".north east) -- (" (name (last conds)) ".north east);"))
      (println (str "\\draw[dotted] (" (name (first conds)) ".south east) -- (" (name (last conds)) ".south east);"))

      (doseq [[n o] (zipmap (map inc (range (count objs))) objs)]
        (println (str "\\node[left] at ($(" (name (last conds)) "-" n "-1)+(-0.5,0)$) {" (name o) "};")))

      (doseq [[n a] (zipmap (map inc (range (count atts))) atts)]
        (println (str "\\node[below,rotate=45,anchor=east] at ($(" (name (last conds)) "-" (count objs) "-" n ")+(0,-0.5)$) {" (name a) "};")))

      (doseq [c conds]
        (println (str "\\node[right] at ($(" (name c) "-" (count objs) "-" (count atts) ")+(0.5,-0.25)$) {" (name c) "};")))
      
      (println "\\end{tikzpicture}")
      )))


;;; write context family to file
(defn- triadic-context-family->latex-contexts-and-tikz
  [cxt-family]
  (let [relative-folder "output/"]
    (do
      (cxt-family->latex cxt-family (str relative-folder "context-family"))
      (->> cxt-family
           (context-family->triadic-context)
           (triadic-context->tikz-picture)
           (spit (str relative-folder "triadic-context-tikz")))
      )))


(defn- triadic-context-family->latex-explored-implications-context
  [cxt-family]
  (let [relative-folder "output/"]
    (->> cxt-family
           (context-family->triadic-context)
           ((fn [tcxt] (explore-all-conditional-theories (triadic-expert-from-triadic-context tcxt)
                                                         (empty-triadic-context-from-triadic-context tcxt)
                                                         (empty-implications-context-from-triadic-context tcxt))))
           (first)
           (#(implcxt->latex % (str relative-folder "explored-implication-context") [:Mo-Fr :Sat :Sun])))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compute C_imp(T)



(defn- context-of-conditional-implications
  "Given a triadic context T, returns the context of conditional implications"
  [T]
  (let [conds (:conditions T)
        atts (:attributes T)
        objs (:objects T)
        holds? (fn [D question] (if (true? ((triadic-expert-from-triadic-context T) D question))
                                  true
                                  false))
        cimplications (for [c conds
                            A (clojure.math.combinatorics/subsets (vec atts))
                           b atts
                           :when (not (clojure.set/subset?  #{b} (set A)))]
                       [(impl/make-implication A #{b}) c])]
    (cxt/make-context
     (map first cimplications)
     conds
     (filter #(holds? #{(second %)} (first %)) cimplications))
    ))


;;;;;;;;;;;;;;;;;;;;;;;
;;; compute the exploration of a triadic context family

(defn- triadic-context-family->explored-domain
  "takes a context family and outputs the exploration result with the context-family as knowledge of the domain expert"
  [cxt-family]
  (->> cxt-family
       (context-family->triadic-context)
       ((fn [tcxt] (explore-all-conditional-theories (triadic-expert-from-triadic-context tcxt)
                                                     (empty-triadic-context-from-triadic-context tcxt)
                                                     (empty-implications-context-from-triadic-context tcxt))))))


;;;;;;;;;;;;;;;;;;;;;;
;;; explore the counterexample to the suggestion by ganter and obiedkov
(def cxt-family6 {:A (cxt/make-context [1] [:a :b ] [[1 :a]])
                  :B (cxt/make-context [1] [:a :b ] [])})
(defn- x []
  (let [tcxt (context-family->triadic-context cxt-family6)
        expert (triadic-expert-from-triadic-context tcxt)
        E0 (empty-triadic-context-from-triadic-context tcxt)
        L0 (empty-implications-context-from-triadic-context tcxt)
        bottom-node (explore-conditions expert [:A :B] E0 L0)]
    bottom-node))
