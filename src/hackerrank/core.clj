(ns hackerrank.core
  (:require [clojure.string :refer [split]]))

;; (defn foo
;;   "I don't do a whole lot."
;;   [x]
;;   (println x "Hello, World!"))

;; (defn palindrome? [string]
;;   (= (seq string) (into '() (seq string))))

;; (defn replace-at [s idx replacement]
;;   (str (subs s 0 idx) replacement (subs s (inc idx))))

;; (defn break-palindrome [pal-string]
;;   (let [res (remove nil?
;;                    (->
;;                     (doall (map (fn [char]
;;                                   (doall
;;                                    (map #(let [new-str
;;                                                (replace-at pal-string % char)]

;;                                            (if (and (not (palindrome? new-str)
;;                                                          )
;;                                                     (pos? (compare pal-string new-str)))
;;                                              new-str
;;                                              nil)
;;                                            )
;;                                         (range (count pal-string)))))
;;                                 (map char (range (int \a) (inc (int \z))))))
;;                     flatten
;;                     sort))]
;;     (if (empty? res) "IMPOSSIBLE"
;;         (nth res 0))))

;; (break-palindrome "acca")

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defn is-edge? [from to start end]
;;   (->> (for [i (range (count from))]
;;     (or (and (= (nth from i) start)
;;              (= (nth to i) end))
;;         (and (= (nth from i) end)
;;              (= (nth to i) start)))
;;     )
;;      (some #{true}))
;;   )

;; (defn flatten-one-level [coll]  
;;   (mapcat  #(if (sequential? %) % [%]) coll))

;; (defn in?
;;   "true if coll contains elm"
;;   [coll elm]  
;;   (some #(= elm %) coll))

;; (defn friendship-score [friends-from friends-to trio]
;;   (->> (map #(for [j (range (count friends-from))]
;;           (if (or (and (= % (nth friends-from j))
;;                     (not (in? trio (nth friends-to j) )))
;;                  (and (= % (nth friends-to j))
;;                     (not (in? trio (nth friends-from j) )))) 1 0)) trio)
;;       flatten
;;       (reduce +))
;; )

;; (defn best-trio [friends-nodes friends-edges friends-from friends-to]
;;   (let [res (->> (for [j (range friends-edges)]
;;                    (for [k (range 1 (inc friends-nodes))]
;;                      (if (and (is-edge? friends-from friends-to
;;                                         (nth friends-to j) k)
;;                               (is-edge? friends-from friends-to k (nth friends-from j))
;;                               (not= (nth friends-to j)
;;                                     (nth friends-from j))
;;                               (not= (nth friends-to j) k)
;;                               (not= (nth friends-from j) k))
;;                        [(nth friends-to j)
;;                         (nth friends-from j)
;;                         k] nil)))
;;                  flatten-one-level
;;                  (remove nil?)
;;                  (map #(friendship-score friends-from
;;                                          friends-to
;;                                          %))
;;                  )]
;;     res
;;     (if (seq res) (apply min res) -1))
;;   )

;; (defn parse-int [s]
;;   (Integer. (re-find  #"\d+" s )))


;; (let [[nodes edges]
;;       (map parse-int (split (read-line) #" "))
;;       from->to (for [n (range edges)] (map parse-int (split (read-line) #" ")))]

;;   (prn (best-trio
;;    nodes
;;    edges
;;    (map #(nth % 0) from->to)
;;    (map #(nth % 1) from->to)))
;;   )


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;; (defn calculate-cost [arr]

  
;;   )

;; (calculate-cost [4 6 2])



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; write a comparator function 'mycompare' that can be
;; used to sort in order of :high then :medium then :low.  It should support
;; other unspecified keywords as lower priority than :low.


;; (defn  mycompare [input1 input2]
;;   (let [order [:low :medium :high]]
;;     (> (.indexOf order input1) (.indexOf order input2))
;;     )
;;   )


;; ;; these should return true:
;; (= (sort mycompare [:high :high :low :medium]) [:high :high :medium :low])
;; (= (sort mycompare [:foo :high :low :medium]) [:high :medium :low :foo])
;; (= (sort mycompare [:low :medium :high :foobar]) [:high :medium :low :foobar])




;; 5/8/2021
;; Interview Preparation

(defn sockMerchant [n ar]
  "Complexity: O(n), (= (count ar) n)
   TOC: ~14 min"
  (reduce + (map (fn [[_ v]] (if (>= v 2) (quot v 2) 0))
       (frequencies ar)))
  #_(->> (map (fn [[k v]] (if (>= v 2) [k (rem v 2)] nil))
          (frequencies ar)) ;; looked up online
     (remove nil?)) ;; looked up online
)

(sock-merchant 7 [10 20 20 10 10 30 50 10 20])


(defn sock-merchant [n ar]
  (reduce (fn [[socks pairs] sock]
            (if (contains? socks sock)
              [(disj socks sock) (inc pairs)]
              [(conj socks sock) pairs]))
          [#{} 0]
          ar))

(->>
 [1 2 1 2 1 3 2]
 (frequencies)
 (map
  (fn [[sock-color cnt]]
                                        ;determine if we have an odd or even number of socks for each color
    (let [cnt' (if (odd? cnt) (dec cnt) cnt)]
                                        ;number of pairs of socks for a color
      (/ cnt' 2))))
                                        ;total of all pairs
 (apply +))

(defn countingvalleys [steps path]
  "complexity: o(n), (= steps n)
   toc: ~ 28 min"
  (loop [path (seq path) dist-from-sea 0 valleys 0] ;; looked up online
    (if path ;; looked up online
      (if (= (first path) \U)
        (recur (next path) (inc dist-from-sea)
               (if (= (inc dist-from-sea) 0) (inc valleys) valleys))
        (recur (next path) (dec dist-from-sea) valleys))
      valleys)))

(countingvalleys 8 "UDDDUDUU")

#_(count
 (sequence
  (comp
                                        ;dedupe by below sea level
   (medley.core/dedupe-by #(neg? %))
                                        ;at sea level
   (filter zero?))
  (reductions +
              [+1 -1 -1 -1 +1 -1 +1 +1])))

;; 1 h
;; 5/8/2021
(defn jumping-on-clouds [c]
  "O(n), (= n (count c))
   Had to look up the algorithm after couldn't do for 1h.
   Was doing something more complicated and O(2^n)"
  """
  (loop [c [[c 0]]]
      (if-not (seq (filter (fn [[path-left steps]] (seq path-left)) c))
        (recur #(map (fn [[path-left steps]]
                       (if (= (second path-left) 0)
                         [(drop 2 path-left) (inc steps)])) c)
               )
        ))

  (map (fn [[path-left steps]]
         [(if (= (second path-left) 0)
            [(drop 2 path-left) (inc steps)])
          (if (= (first path-left) 0)
            [(rest path-left) (inc steps)])
          ])
       [[[1 0 0] 0] [[0 0 1 0] 9]]
       )
"""

  (loop [c (rest c) jumps 0]
    (if (seq c)
      (if (= (second c) 0)
        (recur (drop 2 c) (inc jumps)) ;; looked up drop online
        (recur (rest c) (inc jumps)))
      jumps)))

(defn cloud
  [input]
  (let [jump-small 1 jump-big 2]
    (trampoline
     (fn jump [idx cnt]
       (let [idx' (+ idx jump-big)]
         (if-let [?zero-or-one (get input idx')]
           #(if (zero? ?zero-or-one)                             ;big or small jump?
              (jump idx' (inc cnt))                               ;big!
              (let [idx'' (+ idx jump-small)]                     ;else, small
                (jump idx'' (inc cnt))))
           cnt)))                                                ;else, we are done, return jump count
     0 0)))
(time (jumping-on-clouds [0 0 0 1 0 1 0]))

(time (cloud [0 0 0 1 0 1 0]))

;; 5/9/2021
;; https://www.hackerrank.com/challenges/repeated-string/problem?h_l=interview&playlist_slugs%5B%5D=interview-preparation-kit&playlist_slugs%5B%5D=warmup
(defn repeated-string [s n]
  "Complexity: O(n), (= n (count s))
   TOC: ~26 min"
  (let [string-seq (seq s)
        indices-in-single-string (keep-indexed #(if (= %2 \a) %1) string-seq)
        num-a-in-single-string (-> (filter #(= % \a) string-seq)
                                  ;; looked up counting occurences of \a online
                                   count
                                   )] ;; looked up keep-indexed online. looked up apply max online
    (-> num-a-in-single-string
       (* (quot n (count string-seq)))
       (+ (count (filter #(> (rem n (count string-seq)) %) indices-in-single-string)))
       )))

(repeated-string "aba" 10)

;; https://www.hackerrank.com/challenges/2d-array/problem?h_l=interview&playlist_slugs%5B%5D=interview-preparation-kit&playlist_slugs%5B%5D=arrays
(defn hourglass-sum [arr]
  "Complexity: O(n^2), (= n (count arr))
   TOC: ~21 min"
  (let [arr (to-array-2d arr)]
    (apply max (for [x (range 1 (dec (count arr)))
      y (range 1 (dec (count arr)))]
    (+
     (aget arr y x)
     (aget arr (dec y) x)
     (aget arr (inc y) x)
     (aget arr (dec y) (dec x))
     (aget arr (inc y) (inc x))
     (aget arr (inc y) (dec x))
     (aget arr (dec y) (inc x)))))))

(hourglass-sum [[-9 -9 -9  1 1 1]
                [0 -9  0  4 3 2]
                [-9 -9 -9  1 2 3]
                [0  0  8  6 6 0]
                [0  0  0 -2 0 0]
                [0  0  1  2 4 0]]
               )

;; 5/10/21
;; https://www.hackerrank.com/challenges/ctci-array-left-rotation/problem?h_l=interview&playlist_slugs%5B%5D=interview-preparation-kit&playlist_slugs%5B%5D=arrays&h_r=next-challenge&h_v=zen
(defn rot-left [a d]
  "Complexity: O(n), (= n (count a))
   TOC: ~9m"
  (concat (drop d a) (take d a)))

(rot-left [1 2 3 4 5] 4)

;; https://www.hackerrank.com/challenges/new-year-chaos/problem?h_l=interview&playlist_slugs%5B%5D=interview-preparation-kit&playlist_slugs%5B%5D=arrays&h_r=next-challenge&h_v=zen&h_r=next-challenge&h_v=zen
;; INCOMPLETE
(defn minimum-bribes [q]
  (let [bribes (keep-indexed #(cond (= (inc %1) %2)
                                   0
                                   :else
                                   (if (pos? (- %2 (inc %1)))
                                     (- %2 (inc %1)) 0)) q)]
    (if (seq (filter #(> % 2) bribes))
      "Too chaotic"
      (apply + bribes))
    bribes))

(minimum-bribes [1 2 5 3 7 8 6 4])


;; https://www.hackerrank.com/challenges/minimum-swaps-2/problem?h_l=interview&playlist_slugs%5B%5D=interview-preparation-kit&playlist_slugs%5B%5D=arrays
;; INCOMPLETE
;; 5/12/21
(set! *warn-on-reflection* false)

(defn minimum-swaps [arr]
  "Complexity: O(n), (= n (count arr))
  TOC: ~36m"
  (loop [swap-low-index 0 arr arr num-swaps 0]
    (if (< swap-low-index (count arr))
      (let [unsorted-slice (drop swap-low-index arr)
            lowest-remaining (apply min unsorted-slice)
            swap-high-index (+ swap-low-index (.indexOf unsorted-slice lowest-remaining))]
        #_(prn "low:" swap-low-index ", high:" swap-high-index ", arr:" arr ", unsorted-slice:" unsorted-slice)
        (recur (inc swap-low-index)
               (assoc arr
                      swap-high-index
                      (arr swap-low-index)
                      swap-low-index
                      (arr swap-high-index))
               (if (< swap-low-index swap-high-index)
                 (inc num-swaps)
                 num-swaps)) ;; looked up swap with assoc online
        )
      num-swaps)))

(minimum-swaps [7 1 3 2 4 5 6])

;; INCOMPLETE
(defn array-manipulation [n queries]
  "Complexity: O(n), (= n (* n (count queries)))
   TOC: ~63m"
  (loop [arr (repeat n 0) queries queries]
    (if-let [query (first queries)]
      (recur
       (keep-indexed #(if (and
                          (>= %1 (dec (first query)))
                          (<= %1 (dec (second query))))
                       (+ %2 (nth query 2))
                       %2) arr)
       (rest queries))
      (apply max arr))))

(= (array-manipulation 10 [[1 5 3] [4 8 7] [6 9 1]])
   10)

;; 5/13/21
;; INCOMPLETE
(defn check-magazine [magazine note]
  "Complexity: O(n m), (= n (count magazine)), (= m (count note))
   TOC: ~26m"
  (if (every? true? (map (fn [[k v]]
         (if-let [freq (get (frequencies note) k)]
           (>= v freq)
           true))
                         (frequencies magazine)))
    "Yes" "No") ;; looked up every online
  )

(check-magazine "give me one grand today night" "give one grand today")

(check-magazine "two times three is not four" "two times two is four")

(check-magazine "ive got a lovely bunch of coconuts" "ive got some coconuts")


;; 5/14/21
(defn two-strings [s1 s2]
  "Complexity: O(nm), (= n (count s1)), (= m (count s2))
  TOC: ~30m"
  (if (some true?
        (map (fn [[k _]]
               (contains? (frequencies s1) k)) (frequencies s2)))
    "YES"
    "NO") ;; looked up some true? online
  )

(two-strings "and" "art")

(two-strings "be" "cat")

(defn count-swaps [a]
  (letfn [(swap [a i j] ;; looked up letfn online
            (assoc a i (nth a j) j (nth a i)))]
    (loop [a a num-swaps 0 i 0]
      (if (< i (count a))
        (let [int-loop (loop [a' a j 0 num-swaps' 0]
                         (if (< j (dec (count a)))
                           (if (> (nth a j) (nth a (inc j)))
                             (recur (swap a' j (inc j)) (inc j) (inc num-swaps'))
                             (recur a' (inc j) num-swaps'))
                           [a' num-swaps']))]
          (recur (nth int-loop 0) (+ num-swaps (nth int-loop 1)) (inc i)))
        [num-swaps (nth a 0) (nth a (dec (count a)))]))))

(let [result (count-swaps [4 2 3 1])]
  (prn (str "Array is sorted in " (nth result 0) " swaps.") )
  (prn (str "First Element: " (nth result 1)) )
  (prn (str "Last Element: " (nth result 2)))
  )

(defn alternating-characters [s]
  "TOC: 25m
   Complexity: O(n), (= n (count s))"
  (letfn [(find-indices [s]
                         (loop [s (seq s) indices {:A [] :B []} curr-index 0]
                           (if-not (empty? s)
                             (recur (rest s)
                                    (if (= (first s) \A)
                                      (assoc indices :A (conj (:A indices) curr-index))
                                      (assoc indices :B (conj (:B indices) curr-index)))
                                    (inc curr-index))
                             indices)))
          (count-adjacent [indices]
            (loop [a-indices indices last-char -2 num-adjacent 0]
             (if-not (empty? a-indices)
               (let [curr-char (first a-indices)]
                 (prn curr-char last-char)
                 (recur (rest a-indices) curr-char (if (= curr-char (inc last-char)) (inc num-adjacent)
                                                       num-adjacent)))
               num-adjacent)))]
    (let [indices (find-indices s)]
      (->
       (count-adjacent (:A indices))
       (+ (count-adjacent (:B indices)))))))

(alternating-characters "AAABBAB")

(defn flipping-bits [n]
  "TOC: <1h
   Complexity: O(1), since bounded by the 32 bit limit"
  (let [bin-seq (seq (Long/toBinaryString n)) ;; looked up toBinaryString online
        size (count bin-seq)
        padded-bin-seq (concat (repeat (- 32 size) \0) bin-seq)]
    (loop [padded-bin-seq padded-bin-seq flipped-val 0]
      (if (empty? padded-bin-seq)
        flipped-val
        (recur (rest padded-bin-seq)
               (+ flipped-val
                  (if (= (first padded-bin-seq) \0)
                    (reduce * (repeat (dec (count padded-bin-seq)) 2))
                    0)))))))

(flipping-bits 4294967295)



;; 5/18
;; https://www.hackerrank.com/challenges/luck-balance/problem?h_l=interview&playlist_slugs%5B%5D=interview-preparation-kit&playlist_slugs%5B%5D=greedy-algorithms

(defn luck-balance [k contests]
  (let [unimportant (filter #(= 0 (nth % 1)) contests)
        unimportant-sum (case (count unimportant)
                          0 0
                          1 (nth (first unimportant) 0)
                          (reduce #(+ (nth %1 0)
                                     (nth %2 0))
                                  unimportant))
        sorted-important (->> (filter #(= 1 (nth % 1)) contests)
                            (sort #(< (nth %1 0) (nth %2 0))))]
    (prn
     unimportant-sum
     (loop [sorted-sum 0 sorted-remaining (take k sorted-important)]
       (if (empty? sorted-remaining)
         sorted-sum
         (recur (+ sorted-sum (nth (first sorted-remaining) 0)) (rest sorted-remaining))))

     (loop [sorted-sum 0 sorted-remaining (drop k sorted-important)]
       (if (empty? sorted-remaining)
         sorted-sum
         (recur (+ sorted-sum (nth (first sorted-remaining) 0)) (rest sorted-remaining))))
     )
    (-
     (+
      unimportant-sum
      (loop [sorted-sum 0 sorted-remaining (take k sorted-important)]
        (if (empty? sorted-remaining)
          sorted-sum
          (recur (+ sorted-sum (nth (first sorted-remaining) 0)) (rest sorted-remaining))))
      )
     (loop [sorted-sum 0 sorted-remaining (drop k sorted-important)]
       (if (empty? sorted-remaining)
         sorted-sum
         (recur (+ sorted-sum (nth (first sorted-remaining) 0)) (rest sorted-remaining))))
     )))

(luck-balance 3 [[5 1] [2 1] [1 1] [8 1] [10 0] [5 0]])

(luck-balance 2 [[5 1] [1 1] [4 0]])

;; 2:37
(defn luck-balance
  "Complexity: O(n), (= n (count contests))
  TOC: >2h"
  [k contests]
  (letfn [(sum-firsts [coll]
            (apply + (map first coll)))]
    (let [unimportant (filter (comp zero? second) contests)
          unimportant-sum (sum-firsts unimportant)
          sorted-important (->> contests
                              (filter #(= 1 (second %)))
                              (sort))
          k-sum (sum-firsts (take (- (count sorted-important) k) sorted-important))
          remaining-sum (sum-firsts (drop (- (count sorted-important) k) sorted-important))]
      (- (+ unimportant-sum
            remaining-sum)
         k-sum))))

;; use apply
(luck-balance 3 [[5 1] [2 1] [1 1] [8 1] [10 0] [5 0]])

(luck-balance 2 [[5 1] [1 1] [4 0]])



;; 2:56
;; https://www.hackerrank.com/challenges/insert-a-node-at-a-specific-position-in-a-linked-list/problem?h_l=interview&playlist_slugs%5B%5D=interview-preparation-kit&playlist_slugs%5B%5D=linked-lists
;; 5/19

(definterface ISinglyLinkedListNode
    (getdata [])
    (getnext [])
    (setdata [node-data])
    (setnext [next-ptr]))

(deftype SinglyLinkedListNode [^:volatile-mutable data ^:volatile-mutable next]
    ISinglyLinkedListNode
    (getdata [_] data)
    (getnext [_] next)
    (setdata [_ node-data] (set! data node-data))
    (setnext [_ next-ptr] (set! next next-ptr)))

(definterface ISinglyLinkedList
    (gethead [])
    (gettail [])
    (sethead [list-head])
    (settail [list-tail])
    (insertnode [node-data]))

(deftype SinglyLinkedList [^:volatile-mutable head ^:volatile-mutable tail]
    ISinglyLinkedList

    (gethead [_] head)
    (gettail [_] tail)
    (sethead [_ list-head] (set! head list-head))
    (settail [_ list-tail] (set! tail list-tail))

    (insertnode [this node-data] [
        (def node (SinglyLinkedListNode. node-data nil))
        (if head [(.setnext (.gettail this) node)] (.sethead this node))
        (.settail this node)]))

(defn print-singly-linked-list [node sep fptr]
    (when node
        [
            (spit fptr (.getdata node) :append true)

            (when (.getnext node) (spit fptr sep :append true))

            (print-singly-linked-list (.getnext node) sep fptr)
        ]))

(defn print-list [list-head]
  (loop [head list-head]
    (if head (do
               (prn (.getdata head))
               (recur (.getnext head))))))

(def llist (SinglyLinkedList. nil nil))

(doseq [node-val [11 9 19 10 4]]
  (.insertnode llist node-val)
)

(defn insert-node-at-position
  "Complexity: O(n), where n is the size of the list"
  [llist data position]
  (loop [node llist p 0]
    (if (> (dec position) p)
      (recur (.getnext node) (inc p))
      (.setnext node (SinglyLinkedListNode. data (.getnext node)))))
  llist)


(insert-node-at-position (.gethead llist) 4 1)
(insert-node-at-position (.gethead llist) 20 3)



(print-list (.gethead llist))





