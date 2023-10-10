import Mathlib.Init.Set

structure IRI :=
(value : String)

structure RdfLiteral :=
(value : String)

inductive Blank : Type
| mk

inductive RdfSubject : Type
| uri : IRI → RdfSubject
| blank : Blank → RdfSubject 


inductive RdfObject : Type
| uri : IRI → RdfObject
| blank : Blank → RdfObject 
| literal : RdfLiteral → RdfObject

inductive RdfPredicate : Type
| rdf_type
| rdf_class
| rdf_friend

structure RdfTriple :=
(subj : RdfSubject)
(pred : RdfPredicate)
(obj : RdfObject) 

structure VersionResource :=
(VersionofConceptResourceIRI : string)

def versionResourceToSubject (v: VersionResource) : RdfSubject :=
RdfSubject.uri { value := v.VersionofConceptResourceIRI }

def oslc_config_VersionResource : IRI := { value := "oslc_config:VersionResource" }

def versionResourceTypeTriple (v: VersionResource) : RdfTriple :=
{
  subj := versionResourceToSubject v,
  pred := RdfPredicate.rdf_type,
  obj  := RdfObject.uri oslc_config_VersionResource
}
inductive ConceptResource : Type
| iri : IRI → ConceptResource 

-- Just for learning how to define more abstract collections, like sets
-- Define the predicate function
def hasNonBlankSubject (t: RdfTriple) : Prop :=
match t.subj with
| RdfSubject.blank _ => false
| _ => true


-- Abstract set of all triples (simply the type itself)
def allTriples : Set RdfTriple := Set.univ

-- Define the subset
def nonBlankSubjectTriples : Set RdfTriple := {t | hasNonBlankSubject t}
