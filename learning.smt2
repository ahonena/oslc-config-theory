(set-logic ALL)
(set-option :produce-models true)

(declare-sort BlankNode 0)
(declare-datatype Iri ((mkIri (value String))))
(declare-datatype Literal ((mkLiteral (value String))))

; Parametric triple
; Functions cannot take in parametric types, so we have to declare a new datatype for each arity
; https://stackoverflow.com/questions/69937363/parametric-functions-in-smtlib
( declare-datatypes ((Triple 3)) (( par ( X Y Z) ( ( triple ( subject X ) ( predicate Y ) ( object Z )) ))))

; From https://www.w3.org/TR/rdf11-concepts/#section-rdf-graph
; An RDF triple consists of three components:
;    the subject, which is an IRI or a blank node
;    the predicate, which is an IRI
;    the object, which is an IRI, a literal or a blank node

; I: Iri
; B: BlankNode
; L: Literal
(declare-fun IIBLisLegalTriple ((Triple Iri Iri BlankNode)) Bool)
(declare-fun IILisLegalTriple ((Triple Iri Iri Literal)) Bool)
(declare-fun IIIisLegalTriple ((Triple Iri Iri Iri)) Bool)
(declare-fun BIBisLegalTriple ((Triple BlankNode Iri BlankNode)) Bool)
(declare-fun BILisLegalTriple ((Triple BlankNode Iri Literal)) Bool)
(declare-fun BIIisLegalTriple ((Triple BlankNode Iri Iri)) Bool)


(declare-const aBlankNode BlankNode)
(declare-const myTestTriple (Triple BlankNode Iri Literal))
(assert (= myTestTriple (triple aBlankNode (mkIri "iriValue") (mkLiteral "literalValue"))))

(declare-const myTestTriple_object Literal)
(assert (= myTestTriple_object (object myTestTriple)))
(check-sat)

(get-value (myTestTriple))
(get-value (myTestTriple_object))
