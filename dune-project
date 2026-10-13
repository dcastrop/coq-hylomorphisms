(lang dune 3.22)
(using rocq 0.12)

(name rocq-hylomorphisms)

(generate_opam_files true)

(source (github dcastrop/coq-hylomorphisms))
(authors "David Castro-Perez" "Marco Paviotti" "Michael Vollmer")
(license GPL-3.0-or-later)
(maintainers "David Castro-Perez <David.CastroPerez@rhul.ac.uk>")

(package
 (name rocq-hylomorphisms)
 (synopsis "Hylomorphisms in Rocq")
 (depends
  (rocq-core (>= 9.2))
  rocq-stdlib
  (coq-paco (>= 4.2.3))))
