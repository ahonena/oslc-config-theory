import Mathlib

-- Basic RDF modeling
structure URI := 
(value : string)

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
| Either
| NotApplicable

-- Define a structure to represent a Property Shape:
structure PropertyShape :=
(occurs : Option (List RdfValueType))
(readOnly : Option Bool)
(valueType : RdfValueType)
(representation : RdfRepresentation)
(range : List URI)

-- Define the specific shapes:
def dcterms_contributor_shape : PropertyShape :=
{
    occurs := none, -- implying Zero-or-many
    readOnly := none, -- unspecified
    valueType := RdfValueType.AnyResource,
    representation := RdfRepresentation.Either,
    range := [{value := ("foaf:Agent" : String)}, {value := ("foaf:Person" : String)}]
}


def dcterms_created_shape : PropertyShape :=
{
    occurs := some [], -- implying Zero-or-one
    readOnly := some true, -- true
    valueType := RdfValueType.dateTime,
    representation := RdfRepresentation.NotApplicable,
    range := [] -- Unspecified range
}

def dcterms_creator_shape : PropertyShape :=
{
    occurs := none, -- implying Zero-or-many
    readOnly := some true, -- true
    valueType := RdfValueType.AnyResource,
    representation := RdfRepresentation.Either,
    range := [{value := "foaf:Agent"}, {value := "foaf:Person"}]
}

--inductive NonEmptyList (α : Type) : Type
--| singleton : α → NonEmptyList
--| cons : α → NonEmptyList → NonEmptyList


--inductive Resource : Type
--| ServiceProvider : Resource
--| Service : Resource
--| GlobalConfigurationService : Resource

--inductive Property : Type
--| dcterms_contributor : Property

--structure Server :=
--(implemented_resources : List Resource)

--structure URI := 
--(value : string)

--inductive RdfRepresentation : Type
--| Reference
--| InLine

--def MaybeRdfRepresentation : Type := Option RdfRepresentation

-- Value types:
--inductive RdfValueType : Type
--| RdfResource (uri : Option URI)
--| dateTime
--| XMLLiteral
--| string
--| rdf_boolean

-- Define the generic property with an Option bool for read-only status
--structure ReadOnlyStatus (α : Type) :=
--(value : α)
--(IsReadOnly : Option boolean)  -- some true: read-only, some false: not read-only, none: unspecified

--inductive dcterms_contributor :=
--| mk : dcterms_contributor

--inductive dcterms_created :=
--| mk : dcterms_created

-- Define Component and Baseline using the Property
--structure Component :=
--(dcterms_contributor : List (ReadOnlyStatus dcterms_contributor))
--(dcterms_created : ReadOnlyStatus dcterms_created)

-- ... other properties ...
--inductive Component : Type
--| Option dcterms_created
--|  List dcterms_creator

-- Prefixed Name
-- Occurs
-- Read-only
-- Value-type
-- Representation
-- Range
-- Description

-- Component properties:

-- List dcterms_contributor
-- Option dcterms_created
-- List dcterms_creator
-- Option dcterms_description
-- Option dcterms_identifier
-- Option dcterms_modified
-- List dcterms_subject
-- Option dcterms_title
-- oslc_config_configurations
-- Option oslc_archived
-- Option oslc_instanceShape
-- List oslc_modifiedBy
-- List oslc_serviceProvider
-- Option oslc_shortId
-- Option oslc_shortTitle
-- TODO: nonempty!!!! rdf_type