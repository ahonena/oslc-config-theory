
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