
-- Basic RDF modeling
structure URI := 
(value : String)

inductive Predicate : Type
| name
| age
| friend
-- ... other predicates as needed

structure Triple :=
(subj : URI)
(pred : Predicate)
(obj : URI) -- this is simplified; objects can also be literals or other types

-- Basic Types for RDF values
inductive RdfValueType : Type
| AnyResource
| dateTime
| XMLLiteral
| rdf_string
| rdf_boolean

inductive RdfRepresentation : Type
| Reference
| Inline
| EitherReferenceOrInline

-- Define a structure to represent a Property Shape:
structure PropertyShape :=
(readOnly : Option Bool)
(valueType : RdfValueType)
(representation : Option RdfRepresentation)
(range : List URI)

-- Define the specific shapes:
def dcterms_contributor_shape : PropertyShape :=
{
    readOnly := none, -- unspecified
    valueType := RdfValueType.AnyResource,
    representation := some RdfRepresentation.EitherReferenceOrInline,
    range := [{value := ("foaf:Agent" : String)}, {value := ("foaf:Person" : String)}]
}


def dcterms_created_shape : PropertyShape :=
{
    readOnly := some true, -- true
    valueType := RdfValueType.dateTime,
    representation := none,
    range := [] -- Unspecified range
}

def dcterms_creator_shape : PropertyShape :=
{
    readOnly := some true, -- true
    valueType := RdfValueType.AnyResource,
    representation := RdfRepresentation.EitherReferenceOrInline,
    range := [{value := "foaf:Agent"}, {value := "foaf:Person"}]
}
