;; Copyright (c) Daniel Borchmann. All rights reserved.
;; The use and distribution terms for this software are covered by the
;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;; which can be found in the file LICENSE at the root of this distribution.
;; By using this software in any fashion, you are agreeing to be bound by
;; the terms of this license.
;; You must not remove this notice, or any other, from this software.

(ns conexp.io.util
  (:use conexp.base)
  (:require [clojure.java.io :as io]))

;;;

(defalias reader io/reader)
(defalias writer io/writer)

(defn get-line
  "Reads one line from *in*."
  []
  (read-line))

(defn get-lines
  "Reads n line from *in*."
  [n]
  (doall (take n (repeatedly #(get-line)))))

(defmacro with-in-reader
  "Opens file with reader and binds it to *in*."
  [file & body]
  `(with-open [input# (reader ~file)]
     (binding [*in* input#,
               *read-eval* false]
       ~@body)))

(defmacro with-out-writer
  "Opens file with writer and binds it to *out*."
  [file & body]
  `(with-open [output# (writer ~file)]
     (binding [*out* output#]
       ~@body)))

(defn tmpfile
  "Returns a temporary and unique File object."
  []
  (java.io.File/createTempFile "conexp-clj-" ".tmp"))


;;; Format dispatch framework macro

(defmacro define-format-dispatch
  "Defines for name the functions write-name, read-name,
  add-name-input-format, get-known-name-input-formats and
  find-name-input-format. You can then add new formats with
  add-name-input-format and read-name will automatically dispatch in
  the format determined from its only argument."
  [name]
  (let [add   (symbol (str "add-" name "-input-format")),
        get   (symbol (str "get-known-" name "-input-formats")),
        find  (symbol (str "find-" name "-input-format")),
        write (symbol (str "write-" name)),
        read  (symbol (str "read-" name)),
        get-default-write (symbol (str "get-default-" name "-format")),
        set-default-write (symbol (str "set-default-" name "-format!")),
        list-formats (symbol (str "list-" name "-formats"))]
  `(do
     (let [known-context-input-formats# (ref {})]
       (defn- ~add [name# predicate#]
	 (dosync
	  (alter known-context-input-formats# assoc name# predicate#)))

       (defn- ~get []
	 (keys @known-context-input-formats#))

       (defn- ~find
         ([file#]
            (first
             (for [[name# predicate#] @known-context-input-formats#
                   :when (with-open [in-rdr# (reader file#)]
                           (predicate# in-rdr#))]
               name#)))
         ([file# format#]
            format#))

       nil)

     (let [default-write-format# (atom nil)]
       (defn ~get-default-write
	 ~(str "Returns default write format for " name "s.")
	 []
	 (when (nil? @default-write-format#)
	   (illegal-state "No default write format specified for " ~name "."))
	 @default-write-format#)

       (defn ~set-default-write
	 ~(str "Sets default write format for " name "s to format.")
	 [format#]
	 (reset! default-write-format# format#))

       nil)

     (defmulti ~write
       ~(str "Writes " name " to file using format.")
       {:arglists (list [(symbol "format") (symbol ~name) (symbol "file")]
			[(symbol ~name) (symbol "file")])}
       (fn [& args#]
	 (cond
	  (= 2 (count args#)) ::default-write
	  (= 3 (count args#)) (first args#)
	  :else (illegal-argument "Invalid number of arguments in call to " ~write "."))))
     (defmethod ~write :default [format# _# _#]
       (illegal-argument "Format " format# " for " ~name " output is not known."))
     (defmethod ~write ::default-write [ctx# file#]
       (~write (~get-default-write) ctx# file#))

     (defmulti ~read
       ~(str "Reads " name " from file, automatically determining the format used.")
       {:arglists (list [(symbol "file")] [(symbol "file") (symbol "explicit-format")])}
       (fn [& args#] (apply ~find args#)))
     (defmethod ~read :default
       [file#]
       (illegal-argument "Cannot determine format of " ~name " in " file#))

     (defn ~list-formats
       ~(str "Returns a list of known " name " formats, with the default value as"
             " first element.")
       []
       (let [def#   (~get-default-write),
             other# (sort (filter (fn [x#] (not= x# def#)) (~get)))]
         (conj other# def#)))

     (defmacro ~(symbol (str "define-" name "-input-format"))
       ~(str "Defines input format for " name "s.")
       [~'input-format [~'file] & ~'body]
       `(defmethod ~'~read ~~'input-format
          ([~~'file]
             ~@~'body)
          ([~~'file ~'~'_]
             ~@~'body)))

     (defmacro ~(symbol (str "define-" name "-output-format"))
       ~(str "Defines output format for " name "s.")
       [~'input-format [~'thing ~'file] & ~'body]
       `(defmethod ~'~write ~~'input-format
          [~'~'_ ~~'thing ~~'file]
          ~@~'body))

     nil)))

;;;

nil
