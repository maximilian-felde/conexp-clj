(ns conexp.fca.triadic
  (:require [conexp.fca.contexts :as cxt]
            [conexp.fca.implications :as impl]
            [conexp.fca.exploration :as expl]
            [conexp.base :as base]))

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

(def cxt-family {:mo-fr mo-fr
                 :sa sa
                 :so so})

(defn all-conditional-implication-theory [cond-cxt-family]
  {:intent (keys cond-cxt-family)
   :extent (impl/canonical-base (subposition-context-coll (vals cond-cxt-family))
                                )})








(defn expert [cxt]
  "creates an expert for a context that answers questions with either true or a context containing the first counterexample (by name) known to the expert"
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
                                          (att-deriv premise) (att-deriv conclusion))))}
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

(defn merge-cxt-fams-or-return-true [map]
  (if (every? (vals map))
    true
    ))

;;; todo add context knowledge
(defn explore-context-family
  "cxt-fam: family of contexts {:cxt-name cxt1 :cxt-name2 cxt2 ...} is the expert knowledge of the domain"
  [cxt-fam background-impls]
  (let [atts (cxt/attributes (first (vals cxt-fam)))
        conds (keys cxt-fam)]
    (loop [C (cxt/make-context [] conds [])
           L background-impls
           last (impl/close-under-implications L #{})
           counterexample-cxt-fam (zipmap (keys cxt-fam)
                                          (repeat (cxt/make-context [] atts [])))]
      (if (not last)                    ; is true if next-closed set returns nil (see conexp.base for details)
        {:C C
         :L L
         :cxt-fam counterexample-cxt-fam}
        (let [cxt (subposition-context-coll (vals counterexample-cxt-fam))
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
                  add-C-incidence
                   (for [m (clojure.set/difference new-conc new-prem)
                              k (keys expert-answers)
                              :when (true? (k expert-answers))]
                     [(impl/make-implication new-prem #{m}) k]
                     #_[[new-prem m] k])
                  add-C-objs (for [m (clojure.set/difference new-conc
                                                             new-prem)]
                               (impl/make-implication new-prem #{m})
                               #_[new-prem m])
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
                                       hmap)))))]
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
                ))))))))



;;; 
#_(defn- explore-attributes-with-complete-counterexamples
  "Performs attribute exploration with complete background knowledge"
  [example-ctx background-knowledge handler]
  (loop [implications background-knowledge,
         last         (close-under-implications implications #{}),
         ctx          example-ctx]
    (if (not last)
      {:implications (difference implications background-knowledge),
       :context ctx}
      (let [conclusion-from-last (context-attribute-closure ctx last)]
        (if (= last conclusion-from-last)
          (recur implications
                 (next-closed-set (attributes ctx)
                                  (clop-by-implications implications)
                                  last)
                 ctx)
          (let [new-impl        (make-implication last conclusion-from-last),
                counterexamples (handler ctx implications new-impl)]
            (cond
              (= counterexamples :abort)
              (recur implications nil ctx) ; forget all other sets
              ;;
              counterexamples            ; add counterexample
              (let [new-objs (map first counterexamples)]
                ;; check that new names are not there already
                (when (exists [g new-objs] (contains? (objects ctx) g))
                  (illegal-argument "Got objects as «new objects» in exploration "
                                    "which are already present."))
                (recur implications
                       last
                       (make-context (into (objects ctx) new-objs)
                                     (attributes ctx)
                                     (union (incidence-relation ctx)
                                            (set-of [g m] [[g ms] counterexamples,
                                                           m ms])))))
              ;;
              true                       ; add implication
              (recur (conj implications new-impl)
                     (next-closed-set (attributes ctx)
                                      (clop-by-implications (conj implications new-impl))
                                      last)
                     ctx))))))))
