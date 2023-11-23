(set-logic ALL)
(declare-sort BlankNode 0)
(declare-datatype Iri ((mkIri (value String))))
(declare-datatype Literal ((mkLiteral (value String))))

; Parametric triple
( declare-datatypes ((Triple 3)) (( par ( X Y Z) ( ( triple ( subject X ) ( predicate Y ) ( object Z )) ))))


(declare-fun isLegalTriple (Triple Iri BlankNode Literal) Bool)

(declare-const aBlankNode BlankNode)
(declare-const myTestTriple (Triple BlankNode Iri Literal))
(assert (= myTestTriple (triple aBlankNode (mkIri "iriValue") (mkLiteral "literalValue"))))

(declare-const myTestTriple_object Literal)
(assert (= myTestTriple_object (object myTestTriple)))
(check-sat)

(get-value (myTestTriple))
(get-value (myTestTriple_object))
