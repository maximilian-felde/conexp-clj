;; Copyright (c) Daniel Borchmann. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file LICENSE at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns conexp.io.lattices
  (:use conexp.base
	conexp.fca.lattices
	conexp.io.util)
  (:use [clojure.contrib.io :exclude (with-in-reader)])
  (:import [java.io PushbackReader]))

;;; Input format dispatch

(define-format-dispatch "lattice")
(set-default-lattice-format! :simple)

;;; Formats

;; Simple conexp-clj Format

(add-lattice-input-format :simple
			  (fn [rdr]
			    (= "conexp-clj simple" (.readLine rdr))))

(defmethod write-lattice :simple [_ lat file]
  (with-out-writer file
    (println "conexp-clj simple")
    (prn {:lattice [(base-set lat)
		    (set-of [x y]
			    [x (base-set lat)
			     y (base-set lat)
			     :when ((order lat) [x y])])]})))

(defmethod read-lattice :simple [file]
  (with-in-reader file
    (let [_        (get-line),
	  hash-map (binding [*in* (PushbackReader. *in*)]
		     (read))]
      (apply make-lattice (:lattice hash-map)))))

;;;

nil