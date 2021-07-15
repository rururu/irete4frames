(ns irete.core
  (:use clojure.java.io))

(def iR (object-array 18)) ;RETE Image

(def STRATEGY 0)
(def TEMPL 1)
(def ANET 2)
(def ACNT 3)
(def MINSAL 4)
(def MAXSAL 5)
(def BPLAN 6)
(def ABLINK 7)
(def BCNT 8)
(def BNET 9)
(def FACTS 10)
(def AMEM 11)
(def BMEM 12)
(def CFSET 13)
(def IDFACT 14)
(def FMEM 15)
(def FCNT 16)
(def BIDS 17)

(def TRACE nil)
(def TLONG nil)

(defmacro dbg [x]
  `(let [x# ~x]
    (println "dbg:" '~x "=" x#)
    x#))

(defn vari? [x]
  "Is x variable? Transtime function"
  (and (symbol? x) (.startsWith (name x) "?")))

(defn prod-name [prod]
  "Get name of production"
  (first prod))

(defn salience [prod]
  "Get salience of production"
  (second prod))

(defn lhs [prod]
  "Get left hand side of production"
  (nnext (take-while #(not (=  % '=>)) prod)))

(defn rhs [prod]
  "Get right hand side of production"
  (rest (drop-while #(not (=  % '=>)) prod)))

(defn dissoc-in
  "Dissociates an entry from a nested associative structure returning a new
  nested structure. keys is a sequence of keys. Any empty maps that result
  will not be present in the new structure."
  [m [k & ks]]
  (if ks
    (if-let [nextmap (get m k)]
      (let [newmap (dissoc-in nextmap ks)]
        (if (seq newmap)
          (assoc m k newmap)
          (dissoc m k)))
      m)
    (dissoc m k)))

(defn templ-map [slots]
  "Created sorted map from list of slots with '? values"
  (let [itl (interleave slots (repeat :?))]
    (apply sorted-map itl)))

(defn to-funarg [typ mp]
  ;;(println [:TO-FUNARG typ mp])
  (cons typ (vals (merge ((aget iR TEMPL) typ) mp))))

(defn tree-put [funarg value mem]
  "Put into tree-like from map made memory"
  (vreset! mem (assoc-in @mem funarg value)))

(defn tree-get [funarg mem]
  "Get from tree-like from map made memory"
  (get-in @mem funarg))

(defn tree-rem [funarg mem]
  "Remove from tree-like from map made memory"
  (vreset! mem (dissoc-in @mem funarg)))

(defn tree-match [patt t-mem ctx]
  "Search fact in tree-type memory matching to pattern with respect to ctx"
  ;;(println [:TREE-MATCH :PATT patt :T-MEM t-mem :CTX ctx])
  (loop [pp patt mem t-mem]
    (if (number? mem)
      (let [fids (ctx :?fids)]
        (if (not (some #{mem} fids))
          [[mem (assoc ctx :?fids (cons mem fids))]]))
      (if (seq pp)
        (let [p1 (first pp)
              p2 (or (ctx p1) p1)]
          (cond
           (= p2 :?)
           (mapcat #(tree-match (rest pp) (mem %) ctx) (keys mem))
           (keyword? p2)
           (mapcat #(tree-match (rest pp) (mem %) (assoc ctx p2 %)) (keys mem))
           true
           (if-let [mem2 (mem p2)]
             (recur (rest pp) mem2))) )) )))

(defn template
  "Select template part of condition"
  [condition]
  (if (even? (count condition))
    (butlast condition)
    condition))

(defn mk-funarg [frame]
  "Create Funarg (list of type and odered by TEMPL slot values)
   from frame (list of type and keys with values)"
  (let [[typ & rst] frame
        mp (apply hash-map rst)]
    (to-funarg typ mp)))

(defn to-typmap [[typ & vls]]
  "Create Typmap (list of type and map of slots) from funarg"
  (let [kk (keys ((aget iR TEMPL) typ))
        kv (interleave kk vls)
        mp (apply hash-map kv)]
    [typ mp]))

(defn univars [cond]
  "Reduces all different variables to '?"
  (map #(if (vari? %) :? %) cond))

(defn slot-in-templ [pair typ]
  "For pair of slot and value checks if slot is in template of typ.
   If so returns pair of slot and value else nil"
  ;;(println [:SLOT-IN-TEMPL pair typ])
  (let [templ ((aget iR TEMPL) typ)
        slot (first pair)]
    (if (some #{slot} (keys templ))
      pair
      (println (str "Slot " slot " is not in template " typ "!")))))

(defn add-anet-entry [condition]
  "If condition in a left hand side of a rule is a pattern (not test with a function on the predicate place)
  adds a new entry to the map representing the alpha net."
  (let [cnd (if (= (first condition) 'not)
              (rest condition)
              condition)
        typ (first cnd)
        cnd2 (cons typ (apply concat (filter #(slot-in-templ % typ) (partition 2 (rest cnd)))))
        funarg (mk-funarg (univars (template cnd2)))
        anet (aget iR ANET)
        acnt (aget iR ACNT)]
    (when (nil? (tree-get funarg anet))
      (tree-put funarg @acnt anet)
      (vswap! acnt inc))))

(defn anet-for-pset
  "Build the alpha net for the given production set (rule set) <pset> as a map"
  [pset]
  (doseq [pp pset]
    (if TRACE (println (str "\n" [:PRODUCTION pp])))
    (doseq [condition (lhs pp)]
      (if (and TRACE TLONG) (println [:condition condition]))
      (add-anet-entry condition)) ))

(defn a-indexof-pattern [pattern]
  "Find an alpha memory cell index for a pattern from a left hand side of some rule"
  ;;(println [:A-INDEXOF-PATTERN :PATTERN pattern])
  (let [funarg (mk-funarg (univars pattern))]
    (tree-get funarg (aget iR ANET))))

(defn collect-vars
  "Returns vector of variables in expression"
  ([ex]
   (vec (set (collect-vars ex nil))))
  ([ex yet]
   (cond
    (and (or (seq? ex) (vector? ex) (= (type ex) clojure.lang.PersistentHashSet))
         (not (empty? ex)))
      (collect-vars (first ex) (collect-vars (rest ex) yet))
    (map? ex) (collect-vars (vals ex) yet)
    (vari? ex) (cons ex yet)
    true yet)))

(defn qq [aa vars]
  "Add call to quote for symbols not variables"
  (let [f1 (fn [x]
             (cond
              (some #{x} vars) x
              (vari? x) x
              (symbol? x) (list 'quote x)
              true  x))]
    (map f1 aa)))

(defn and-or [x vrs]
  "Translate list-vector form of condition to and-or form"
  ;;(println [:AND-OR x vrs])
  (cond
   (list? x)
     (cond
      (symbol? (first x)) (cons (first x) (qq (rest x) vrs))
      true (cons 'and (map #(and-or % vrs) x)))
   (vector? x) (cons 'or (map #(and-or % vrs) x))
   true x))

(defn mk-test-func [tst vrs]
  (let [aof (and-or tst vrs)
        df (list 'fn vrs aof)]
    (if TRACE (println [:TEST-FUNCTION df]))
    (let [cf (eval df)]
      (if (and TRACE TLONG) (println [:COMPILED cf]))
      cf)))

(defn var-to-key [e]
  (if (keyword? e)
    (do (println (str "Keywords forbidden in LHS: " e)) (name e))
    (if (and (symbol? e) (.startsWith (name e) "?"))
      (keyword e)
      e)))

(defn mk-pattern-and-test [condition]
  "Make pattern or test"
  ;;(println [:MK-PATTERN-AND-TEST condition])
  (if (= (first condition) 'not)
    (let [[apid patt] (mk-pattern-and-test (rest condition))]
      [apid (cons 'not patt)])
    (let [[frame test]
            (if (even? (count condition))
              [(butlast condition) (last condition)]
              [condition nil])
          rst (if test
                (let [vrs (collect-vars test)
                      vks (map keyword vrs)]
                  [vks (mk-test-func test vrs)])
                [nil nil])
          frame (map var-to-key frame)
          patt (cons (mk-funarg frame) rst)
          apid (a-indexof-pattern (template condition))]
        (list apid patt))))

(defn enl [lst]
  "Add numbers to lists"
  (map cons (range (count lst)) lst))

(defn mk-rhs-func [vrs rhs]
  "Create function from vector of variables and right hand side"
  ;;(println [:MK-RHS-FUNC vrs rhs])
  (let [df (cons 'fn (cons vrs rhs))]
    (if TRACE (println [:RHS-FUNCTION df]))
    (let [cf (eval df)]
      (if (and TRACE TLONG) (println [:COMPILED cf]))
      cf)))

(defn beta-net-plan
  "Create a plan of the beta net that will be used to its building.
   The plan describes the beta net as a list, mean while the real beta net is an array.
   The plan is the list of lists each of which represents one cell of the beta memory.
   First element of each list is an index of the beta memory, rest of each list is a content of the corresponding cell.
   Recalculate salience into positive for using as CFARR index"
  ([pset]
    (enl (mapcat
           #(beta-net-plan
             (prod-name %)
             (- 0 (salience %))
             (lhs %)
             (rhs %))
           pset)))
  ([pname sal lhs rhs]
    (if TRACE (println (str "\n" [:PRODUCTION pname])))
    (let [pts (map mk-pattern-and-test lhs)
          fir (concat (first pts) [pname])
          mid (butlast (rest pts))
          vrs (collect-vars rhs)
          las (concat (last pts)
                      (list pname sal (map keyword vrs) (mk-rhs-func vrs rhs)))]
      (if (= (count lhs) 1)
        (list (cons 'ex las))
        (concat (list (cons 'e fir))
                (map #(cons 'i %) mid)
                (list (cons 'x las)) )) )))

(defn fill-ablink
  "Fill alpha-beta links table from beta net plan,
  separately alpha-beta links map for negative patterns"
  ([bplan ablink]
    (dotimes [i (count ablink)]
      (fill-ablink bplan ablink i)))
  ([bplan ablink i]
    (let [flt (filter #(= (nth % 2) i) bplan)
          nnot (filter #(not= (first (nth % 3)) 'not) flt)]
      (aset ablink i (map first nnot)))))

(defn fill-bnet [bnet bplan]
  "Fill beta net from beta net plan"
  (doseq [[i & v] bplan]
    (aset bnet i v)))

(defn log-lst [path x]
  "Log list"
  (let [fos (writer path)]
    (doall (map #(.write fos (str % "\n")) x))
    (.close fos)))

(defn log-anp [path x]
  "Log Alpha Net Plan"
  (let [fos (writer path)]
    (doseq [[k v] (into {} x)]
      (.write fos (str k ":" "\n"))
      (doseq [[k2 v2] v]
        (.write fos (str " " k2 ": " v2 "\n"))))
    (.close fos)))

(defn log-array [path a]
  "Log array"
  (let [fos (writer path)]
    (dotimes [i (count a)]
      (.write fos (str i " " (seq (aget a i)) "\n")))
    (.close fos)))

(declare reset)

(defn create-rete [tset pset]
  "Creates RETE image from a production set and reset it"
  (def iR (object-array 18))
  (aset iR STRATEGY 'DEPTH) ;; Default strategy. Alternative 'BREADTH
  (if TRACE (println "\n.... Creating TEMPLATES for Pset ....\n"))
  (aset iR  TEMPL
    (apply hash-map (mapcat #(list (first %) (templ-map (rest %))) tset)))
  (if TRACE (println "\n.... Creating ANET PLAN for Pset ...."))
  (aset iR  ANET (volatile! {}))
  (aset iR ACNT (volatile! 0))
  (anet-for-pset pset)
  (when TRACE
    (log-anp "alpha-net-plan.txt" @(aget iR ANET))
    (println "\n.... Creating BNET PLAN for Pset ...."))
  (aset iR MINSAL (apply min (map salience pset)))
  (aset iR MAXSAL (apply max (map salience pset)))
  (aset iR BPLAN (beta-net-plan pset))
  (when TRACE
    (log-lst "beta-net-plan.txt" (aget iR BPLAN))
    (println "\n.... Creating BNET ANET LINK PLAN for Pset ....\n"))
  (aset iR ABLINK (object-array @(aget iR ACNT)))
  (aset iR BCNT (count (aget iR BPLAN)))
  (aset iR BNET (object-array (aget iR BCNT)))
  (fill-bnet (aget iR BNET) (aget iR BPLAN))
  (fill-ablink (aget iR BPLAN) (aget iR ABLINK))
  (when TRACE
    (log-array "alpha-beta-links.txt" (aget iR ABLINK))
    (println "\n.... Log Files Created ....\n"))
  (reset)
  (if TRACE (println "\n.... RETE Created and Reset ....\n"))
  [@(aget iR ACNT) (aget iR BCNT)])

(defn reset []
  "Reset: clear and initialize all memories"
  (aset iR  AMEM (object-array @(aget iR ACNT)))
  (dotimes [i (alength (aget iR AMEM))] (aset (aget iR AMEM) i [nil (volatile! {})]))
  (aset iR BMEM (object-array (aget iR BCNT)))
  (aset iR CFSET (volatile! (sorted-map)))
  (aset iR IDFACT (volatile! {}))
  (aset iR FMEM (volatile! {}))
  (aset iR FCNT (volatile! 0))
  (aset iR BIDS (volatile! {})))

(defn mk-fact [funarg]
  "Make fact. Returns new fact [funarg id] id or nil if same fact exists"
  ;;(println [:MK-FACT funarg])
  (let [fmem (aget iR FMEM)]
    (if (nil? (tree-get funarg fmem))
      (let [fcnt (aget iR FCNT)
            fid @fcnt]
        (tree-put funarg fid fmem)
        (vswap! (aget iR IDFACT) assoc fid funarg)
        (vswap! fcnt inc)
        [funarg fid]))))

(defn var-vals [mp vrs]
  "Takes values from context map mp in order of list of variables"
  (map #(mp %) vrs))

(defn try-func-add-fid [func fid ctx vrs bi]
  ;;(println [:TRY-FUNC-ADD-FID func fid ctx vrs bi])
  (if (or (nil? func) (apply func (var-vals ctx vrs)))
    (let [bds (aget iR BIDS)
          bids (get @bds fid)]
      (if (not (some #{bi} bids))
        (vreset! bds (assoc @bds fid (cons bi bids))))
      ctx)))

(defn match-fact-to-pattern [ffuar pfuar]
  "Match funarg of fact to funarg of pattern"
  ;;(println [:MATCH-FACT-TO-PATTERN ffuar pfuar])
  (every? #(= % true)
          (map (fn [x y] (or (= x y) (keyword? y)))
               ffuar
               pfuar)))

(defn ground-match [gargs fargs ctx]
  "Match grounded arguments of pattern with arguments of fact.
  Return updated context"
  ;;(println [:GROUND-MATCH gargs fargs ctx])
  (if (empty? gargs)
    ctx
    (let [[g & rgs] gargs
          [f & rfs] fargs]
      (ground-match rgs rfs (if (and (keyword? g) (not= g :?) (not= f :?))
                              (assoc ctx g f)
                              ctx)))))

(defn matched-context [[f & fargs] [p & pargs] ctx]
  "Returns matched context for given fact, pattern and initial context"
  ;;(println [:MATCHED-CONTEXT [f fargs] [p pargs] ctx])
  (if (= f p)
    (let [gargs (map #(or (ctx %) %) pargs)]
      (if (match-fact-to-pattern fargs gargs)
        (merge ctx (ground-match gargs fargs {}))))))

(defn matched-ctx [[ffuar fid] [pfuar vrs func] ctx bi]
  "Match fact with pattern with respect to context"
  ;;(println [:matched-ctx ffuar fid pfun pargs vrs func ctx bi])
  (let [fids (ctx :?fids)]
    (if (not (some #{fid} fids))
      (if-let [ctx2 (matched-context ffuar pfuar ctx)]
        (try-func-add-fid func fid (assoc ctx2 :?fids (cons fid fids)) vrs bi)) ) ))

(defn match-ctx-amem [amem [pfuar vrs func] ctx bi]
  "Match list of facts with pattern with respect to context and beta cell.
  Returns matching contexts"
  ;;(println [:MATCH-CTX-AMEM amem pfuar vrs func ctx bi])
  (if-let [mm (seq (tree-match pfuar @amem ctx))]
    (filter some?
            (for [[fid ctx2] mm]
              (try-func-add-fid func fid ctx2 vrs bi)) ) ))

(defn mk-match-list [amem pattern ctx-list bi]
  "Make match-list of contexts"
  ;;(println [:MK-MATCH-LIST amem pattern ctx-list bi])
  (if (not (empty? @amem))
    (mapcat #(match-ctx-amem amem pattern % bi) ctx-list)))

(defn averfid [ctx]
  "Evaluation of activation assesment 'average fid' depending on strategy"
  (let [fids (ctx :?fids)
        sum (apply + fids)
        k (/ sum (count fids))]
    (if (= (aget iR STRATEGY) 'DEPTH)
      (- k)
      k)))

(defn print-cfset []
  (doseq [[k v] (seq @(aget iR CFSET))]
    (println [k (map ffirst v)])))

(defn add-to-confset [aprod match-list]
  "Add activation to conflict set array"
  ;;(println [:ADD-TO-CONFSET (first aprod) (type (first aprod)) :ML (map #(get % :?fids) match-list)])
  (let [new (map #(vector aprod %) (sort-by averfid match-list))
        sal (salience aprod)
        cfs (aget iR CFSET)
        old (get @cfs sal)
        uni (if (= (aget iR  STRATEGY) 'DEPTH)
              (concat new old)
              (concat old new))]
    (vswap! cfs assoc sal uni)))

(declare activate-b)

(defn activate-b-not [bi amem eix pattern tail ctx-list]
  "Activate beta net cell for not node
  Add to all contexts alpha memory cell and pattern to not match when activated"
  ;;(println [:ACTIVATE-B-NOT bi amem eix pattern tail bi (count ctx-list)])
  (let [ml (map #(assoc % :not-match (conj (or (:not-match %) []) [amem pattern])) ctx-list)]
    (condp = eix
      'x (add-to-confset tail ml)
      'i (activate-b (inc bi) ml))))

(defn activate-b [bi ctx-list]
  "Activate beta net cell of index <bi> with respect to a list of contexts
  already activated by a new fact with an index <new-fid>"
  ;;(println [:ACTIVATE-B :BI bi :CTX-LIST ctx-list])
  (let [bnode (aget (aget iR BNET) bi)
        [eix bal pattern & tail] bnode
        amem (aget iR AMEM)]
    (if (= (first pattern) 'not)
      (activate-b-not bi (second (aget amem bal)) eix (rest pattern) tail ctx-list)
      (let [ml (mk-match-list (second (aget amem bal)) pattern ctx-list bi)]
        (if (seq ml)
          (condp = eix
            'x (add-to-confset tail ml)
            'i (let [bmem (aget iR BMEM)]
                 (aset bmem bi (concat ml (aget bmem bi)))
                 (activate-b (inc bi) ml))) )) )))

(defn entry-a-action [bi pattern b-mem new-fact]
  "Entry alpha activation"
  ;;(println [:ENTRY-A-ACTION :BI bi :PATTERN pattern :BMEM b-mem :NEW-FACT new-fact])
  (when-let [ctx (matched-ctx new-fact pattern {} bi)]
    (aset (aget iR BMEM) bi (cons ctx b-mem))
    (activate-b (inc bi) (list ctx))))

(defn inter-a-action [bi pattern b-mem new-fact]
  "Intermediate alpha activation"
  ;;(println [:INTER-A-ACTION :BI bi :PATTERN pattern :BMEM b-mem :NEW-FACT new-fact])
  (let [bmem (aget iR BMEM)]
    (if-let [ctx-list (seq (aget bmem (dec bi)))]
      (when-let [ml (seq (keep #(matched-ctx new-fact pattern % bi) ctx-list))]
        (aset bmem bi (concat ml b-mem))
        (activate-b (inc bi) ml)))))

(defn exit-a-action [bi pattern tail b-mem new-fact]
  "Exit alpha activation"
  ;;(println [:EXIT-A-ACTION :BI bi :PATTERN pattern :TAIL tail :NEW-FACT new-fact])
  (let [bmem (aget iR BMEM)]
    (if-let [ctx-list (seq (aget bmem (dec bi)))]
      (when-let [ml (seq (keep #(matched-ctx new-fact pattern % bi) ctx-list))]
        (aset bmem bi (concat ml b-mem))
        (add-to-confset tail ml)))))

(defn enex-a-action [bi pattern tail new-fact]
  "Entry and exit alpha activation (for LHS with 1 pattern)"
  ;;(println [:ENEX-A-ACTION :PATTERN pattern :TAIL tail :NEW-FACT new-fact])
  (if-let [ctx (matched-ctx new-fact pattern {} bi)]
    (add-to-confset tail (list ctx)) ))

(defn activate-a
  "Activate alpha net cells for index list <ais>"
  [ais]
  ;;(println [:ACTIVATE-A :AIS ais])
  (doseq [ai ais]
    (let [ablinks (aget (aget iR ABLINK) ai)
          bnms (map #(list % (aget (aget iR BNET) %) (aget (aget iR BMEM) %)) ablinks)
          new-fact (first (aget (aget iR AMEM) ai))]
      (doseq [[bi [eix bal pattern & tail] b-mem] bnms]
        (condp = eix
          'e (entry-a-action bi pattern b-mem new-fact)
          'ex (enex-a-action bi pattern tail new-fact)
          'i (inter-a-action bi pattern b-mem new-fact)
          'x (exit-a-action bi pattern tail b-mem new-fact))) )))

(defn a-indices
  "For an asserted funarg find all suitable alpha memory cells"
  ([[fun & args]]
   (if-let [anet (@(aget iR ANET) fun)]
     (a-indices args anet)))
  ([args anet]
   (letfn [(path [args key anet]
                 (if (or (= key :?) (= key (first args)))
                   (a-indices (rest args) (anet key))))]
     (if (number? anet)
       [anet]
       (mapcat #(path args % anet) (keys anet))))))

(defn remove-ctx-with [fid ctxlist]
  "Remove context for given fact id"
  ;;(println [:REMOVE-CTX-WITH :FID fid :CTXLIST ctxlist])
  (doall (filter #(not (some #{fid} (:?fids %))) ctxlist)))

(defn retract-b [fid bis]
  "Retract fact id from the beta memory:
  from bi cell and down cells to end of rule"
  ;;(println [:RETRACT-B :FID fid :BIS bis])
  (let [bmem (aget iR BMEM)]
    (doseq [bi bis]
      (loop [i bi]
        (aset bmem i (remove-ctx-with fid (aget bmem i)))
        (let [ni (inc i)]
          (if (< ni (aget iR BCNT))
            (let [eix (first (aget (aget iR BNET) ni))]
              (if (or (= eix 'i) (= eix 'x))
                (recur ni))) ))) )))

(defn remove-fmem [fid]
  "Remove fact from facts memory by fact id.
  Returns funarg of removed fact"
  (let [funarg (@(aget iR IDFACT) fid)]
    (when (seq? funarg)
      (tree-rem funarg (aget iR FMEM))
      funarg)))

(defn retract-fact [fid]
  "Retract fact for given fact-id by removing it from alpha, beta and fact memory."
  ;;(println [:RETRACT-FACT fid])
  (if-let [funarg (remove-fmem fid)]
    (let [ais (a-indices funarg)
          amem (volatile! {})
          bds (aget iR BIDS)]
      (vswap! (aget iR IDFACT) dissoc fid)
      (retract-b fid (get @bds fid))
      (vswap! bds dissoc fid)
      (doseq [ai ais]
        (tree-rem funarg (second (aget (aget iR AMEM) ai)) ))
      (if TRACE
        (if TLONG
          (println [:<== :fid fid (to-typmap funarg)])
          (print " <-" fid)))
      funarg)))

(defn ais-for-funarg [funarg]
  "Create fact from funarg and add it to alpha memory.
   Returns list of activated alpha memory cells"
  ;;(println [:AIS-FOR-FUNARG funarg])
  (if-let [fact (mk-fact funarg)]
    (when-let [ais (a-indices funarg)]
      (if TRACE
        (if TLONG
          (println [:==> :fid (second fact) (to-typmap funarg)])
          (print " ->" (second fact))))
      (doseq [ai ais]
        (let [amm (aget iR AMEM)
              amem (second (aget amm ai))]
          (tree-put funarg (second fact) amem)
          (aset amm ai [fact amem])))
      ais)))

(defn assert-frame [frame]
  "Assert frame and activate corresponding alpha nodes"
  ;;(println [:ASSERT-FRAME frame])
  (activate-a (ais-for-funarg (mk-funarg frame))))

(defn modify-fact [fid mmp]
  "Modify fact for given fact-id by retracting it and asserting, modified frame"
  ;;(println [:MODIFY-FACT fid mmp])
  (if-let [funarg (retract-fact fid)]
    (let [[typ mp] (to-typmap funarg)
          mp2 (merge mp mmp)
          ais (ais-for-funarg (to-funarg typ mp2))]
      (activate-a ais))))

(defn assert-list
  "Function for assertion a list of triples or object descriptions (see comments on the function 'asser').
   For the use outside of the right hand side of rules"
  [lst]
  (activate-a (set (mapcat ais-for-funarg lst))))

(defn not-match-ctx-amem [amem [pfuar vrs func] ctx]
  "If not match context alpha memory returns it with remembered what was not matched"
  ;;(println [:NOT-MATCH-CTX-AMEM :AMEM amem :PFUAR pfuar :VRS vrs :FUNC func :CTX ctx])
  (or (empty? amem)
      (let [mm (tree-match pfuar amem ctx)]
        (or (empty? mm)
            (and func
                 (empty? (filter #(apply func (var-vals % vrs)) (map second mm))))))))

(defn all-not-matched [nm-lst ctx]
  "Is this context for which all not matched earlier are not matched now"
  (or (empty? nm-lst)
      (every? #(let [[amem pvf] %]
                 (not-match-ctx-amem @amem pvf ctx)) nm-lst)))

(defn resolve-not-matched [acs]
  "First activation with context that not extinct and
  has all not matched negative conditions"
  ;;(println [:RESOLVE-NOT-MATCHED (count acs)])
  (loop [[[aprod ctx :as act] & tail] acs head []]
    (if (seq act)
      (cond
        (some #(nil? (@(aget iR IDFACT) %)) (ctx :?fids))
        (recur tail head)
        (all-not-matched (:not-match ctx) ctx)
        [[aprod ctx] (concat head tail)]
        true
        (recur tail (conj head act)))
      [:no-activations])))

(defn resolve-conf-set [cfset]
  "Resolve whole conflict set"
  (if (seq cfset)
    (let [[sal acs] (first cfset)
          [rsv rst] (resolve-not-matched acs)]
      (cond
        (= rsv :no-activations)
        (do (vswap! (aget iR CFSET) dissoc sal) nil)
        (seq rsv)
        (do (vswap! (aget iR CFSET) assoc sal rst) rsv)
        true
        (resolve-conf-set (rest cfset))))))

(defn fire-resolved [[prod ctx]]
  "Fire resolved production with ctx"
  ;;(println [:FIRE-RESOLVED prod ctx])
  (let [[pnam sal vars func] prod]
    (when TRACE
      (println)
      (if TLONG
        (println [:FIRE pnam :CONTEXT (dissoc ctx :not-match)])
        (print "FIRE:" pnam (get ctx :?fids))))
    (apply func (var-vals ctx vars))))

(defn fire
  "Fire!"
  ([]
   (while (not (every? empty? (vals @(aget iR CFSET))))
     (fire 1)))
  ([n]
    (dotimes [i n]
      (if-let [reso (resolve-conf-set (seq @(aget iR CFSET)))]
        (fire-resolved reso)))))

(defn asser
  "Function for the facts assertion that can be used in the right hand side of the rule.
   It has arbitrary number of arguments that as a whole represent a frame"
  [& args]
  (assert-frame args))

(defn retract [fids & indices]
  "Function for the facts retraction that can be used in the right hand side of the rule.
   Retract facts for indices of patterns in left hand side of rule"
  ;;(println [:RETRACT fids indices])
  (let [fids (reverse fids)]
    (doseq [idx indices]
      (retract-fact (nth fids idx)))))

(defn modify [fids idx & svals]
  "Function for the fact modification that can be used in the right hand side of the rule.
   Modify fact for given index of pattern in left hand side of rule"
  ;;(println [:MODIFY fids idx svals])
  (let [fids (reverse fids)]
    (modify-fact (nth fids idx) (apply hash-map svals))))

(defn fact-id [fids & indices]
  "Function for getting fact id that can be used in the right hand side of the rule"
  (let [fids (reverse fids)]
    (int (nth fids (first indices)))))

(defn problem-solved []
  "Function for clearing conflict set that can be used in the right hand side of the rule"
  (vreset! (aget iR CFSET) (sorted-map)))

(defn frame-by-id [fid]
  "Extracts frame for fact id from facts memory"
  (if-let [funarg (@(aget iR IDFACT) fid)]
    (let [[typ mp] (to-typmap funarg)]
      (cons typ (apply concat (seq mp))) )))

(defn fact-list
  "List of facts (of some type)"
  ([]
   (filter #(not= (second %) nil)
           (for [i (range @(aget iR FCNT))](cons i (frame-by-id i)))))
  ([typ]
   (filter #(= (second %) typ) (fact-list))))

(defn facts
  "Prints facts  (of some type)"
  ([]
   (let [fl (fact-list)]
     (doall (map println fl))
     (count fl)))
  ([typ]
   (let [fl (fact-list typ)]
     (doall (map println fl))
     (count fl))))

(defn ppr [typ]
  "Pretty prints facts of type typ or all facts when typ = :all"
  (let [all (fact-list)
        sel (if (= typ :all) all (filter #(= (second %) typ) all))]
    (doseq [fact sel]
      (println)
      (let [[[n typ] & rp] (partition-all 2 fact)]
        (println (str "Fact" n " " typ))
        (doseq [sv rp]
          (println (str "  " (first sv) " " (second sv))) )) )
    (count sel)))

(defn trace []
  "Begins tracing of translation and execution"
  (def TRACE true))

(defn untrace []
  "Ends tracing of translation and execution"
  (def TRACE nil))

(defn trans-asser [x vars]
  (cons 'irete.core/asser (qq (rest x) vars)))

(defn trans-retract [x mp]
  (cons 'irete.core/retract
        (cons '?fids
               (map #(mp %) (rest x)))))

(defn trans-modify [x vars mp]
  (cons 'irete.core/modify
        (cons '?fids
                (cons (mp (first (rest x)))
                      (qq (nnext x) vars)))))

(defn trans-fact-id [x mp]
  (cons 'irete.core/fact-id
        (cons '?fids
               (map #(mp %) (rest x)))))

(defn trans-problem-solved []
  '(irete.core/problem-solved))

(defn destruct [v]
  "Destructuring support: collect symbols inside vectors"
  (cond
   (vector? v) (mapcat destruct v)
   (= v '&) []
   true [v]))

(declare trans-rhs)

(defn trans-let [x vars mp]
  (let [binds (second x)
        pairs (partition 2 binds)
        vars2 (map first pairs)
        vals2 (map second pairs)
        vars3 (mapcat destruct (vec vars2))
        vals3 (map #(trans-rhs % vars mp) vals2)
        binds (vec (interleave vars2 vals3))
        vars4 (concat vars vars3)]
    (cons (first x)
          (cons binds (trans-rhs (nnext x) vars4 mp)))))

(defn trans-lhs [lhs]
  "Translate left hand side of rule by removing statement labels and put them into map.
    Returns map of statement labels with statement indexes"
  (loop [i 0 ss lhs mp {} nlhs []]
    (if (seq ss)
      (let [los (first ss)]
        (if (symbol? los)
          (recur (inc i) (nnext ss) (assoc mp los i) (conj nlhs (first (next ss))))
          (recur (if (not= (first los) 'not) (inc i) i) (next ss) mp (conj nlhs los))))
      [nlhs mp])))

(defn trans-rhs [x vars mp]
  "Translate right hand side of rule by replacing in retract and modify statements
   labels of left hand side statements with their indexes using corresponding map"
  ;;(println [:TRANS-RHS x (type x) vars mp])
  (cond
   (seq? x)
     (condp = (first x)
      'asser (trans-asser x vars)
      'retract (trans-retract x mp)
      'modify (trans-modify x vars mp)
      'fact-id (trans-fact-id x mp)
      'problem-solved (trans-problem-solved)
      'let (trans-let x vars mp)
      'if-let (trans-let x vars mp)
      'when-let (trans-let x vars mp)
      'loop (trans-let x vars mp)
      (map #(trans-rhs % vars mp) x))
   (vector? x) (vec (map #(trans-rhs % vars mp) x))
   true x))

(defn trans-rule [rule]
  "Translate rule by translating lhs and rhs of rule"
  (let [nam (prod-name rule)
        sal (salience rule)
        lsd (lhs rule)
        rsd (rhs rule)
        [lsd2 mp] (trans-lhs lsd)
        rsd2 (trans-rhs rsd nil mp)]
    (concat [nam] [sal] lsd2 ['=>] rsd2)))

(defn slurp-with-comments [f]
  "Opens a reader on f and reads all its contents, returning a string.
  Skip rest of the line starting from semicolon."
  (let [sb (StringBuilder.)]
    (with-open [^java.io.Reader r (reader f)]
      (loop [c (.read r) comm false]
        (if (neg? c)
          (str sb)
          (let [cc (char c)
                is-comm (or (and (not comm) (= cc \;)) (and comm (not= cc \newline)))]
            (if (not is-comm)
              (.append sb cc))
            (recur (.read r) is-comm)) ))) ))

(defn strategy-depth
  "Set conflict resolution strategy to depth in current or specified image"
  ([]
   (aset iR  STRATEGY 'DEPTH))
  ([image]
   (aset image  STRATEGY 'DEPTH)))

(defn strategy-breadth
  "Set conflict resolution strategy to breadth in current or specified image"
  ([]
   (aset iR  STRATEGY 'BREADTH))
  ([image]
   (aset image  STRATEGY 'BREADTH)))

(defn slot-value [s f]
  "Returns value of slot of fact (as of item of result of the function fact-list)"
  (s (apply hash-map (rest (rest f)))))

(defn facts-with-slot-value
  "Returns list of facts with slot values for which (f slot-value value) = true"
  ([slot f value]
   (facts-with-slot-value :all slot f value (fact-list)))
  ([typ slot f value]
   (facts-with-slot-value typ slot f value (fact-list typ)))
  ([typ slot f value facts]
   (filter #(f (slot-value slot %) value) facts)))

(defn create-rete-image
  "Creates RETE from templates and rules and set all necessary constants describing RETE and facts (and funcs)"
  ([temps rules facts]
   (create-rete temps (filter some? (map trans-rule rules)))
   (aset iR FACTS (volatile! facts)))
  ([temps rules facts funcs]
   (let [ons (ns-name *ns*)]
    (eval (cons 'do funcs))
    (in-ns ons)
    (create-rete-image temps rules facts))))
    
(defn clone-rete-image []
  (let [cpi (java.util.Arrays/copyOf iR (count iR))]
    (reset)
    cpi)) 
        
(defn get-rete-image []
  "Returns a vector of all necessary constants describing RETE and facts"
  iR)
  
(defn set-rete-image [image]
  "Set values of all necessary constants describing RETE and facts from the vector"
  (def iR image))

(defn step
  "Step through facts in current rete image"
  ([]
   (if (not (every? empty? (vals @(aget iR CFSET))))
     (fire 1)
     (let [facts (aget iR FACTS)]
      (if (seq @facts)
       (do (assert-frame (first @facts))
         (vswap! facts rest)
         (fire 1))
       (println "No facts!")))))
  ([n]
   (dotimes [i n]
     (step))))

(defn run
  "With specified rete image assert facts and fire one by one"
  ([]
   (run iR))
  ([image]
   (run image @(aget image FACTS)))
  ([image facts]
   (def iR image)
   (doseq [f facts]
     (assert-frame f))
     (fire)
     (if (and TRACE (not TLONG))
       (println))))
       
(defn tst [N path trace tlong]
  (def TRACE trace)
  (def TLONG tlong)
  (def mab (read-string (slurp-with-comments path)))
  (def fct (rest (nth mab 3)))
  (def fun (rest (nth mab 2)))
  (def rls (rest (second mab)))
  (def tmp (rest (first mab)))
  (if (seq fun)
    (create-rete-image tmp rls fct fun)
    (create-rete-image tmp rls fct))
  (def irs (cons iR (for [i (range N)] (clone-rete-image))))
  (println "Images" (count irs))
  (time 
    (doseq [i irs] (run i))))

;; The End

