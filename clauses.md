| Clause number     | Description |
| ----------- | ----------- |
| CONFIG-VR-1 |	A version resource defines a particular version of the state of a concept resource. Not every past state is necessarily kept. A server MAY elide or discard states.
CONFIG-VR-2 |	A version resource MUST have a type of oslc_config:VersionResource.
CONFIG-VR-3 |	A version resource MUST be related to its concept resource using the dcterms:isVersionOf property.
CONFIG-VR-4 |	Version resources SHOULD be compliant with [LDP].
CONFIG-VR-5 |	Version resources SHOULD have an oslc_config:versionId property.
CONFIG-VR-7 |	The shape of a versioned resource: all versioned resources MUST match this shape
CONFIG-VR-8 |	Versioned resources SHOULD match other shapes appropriate for their types - that is, they MAY have additional properties and property constraints beyond those defined here
CONFIG-VR-9 |	Each resource SHOULD have one instance of the dcterms:created property
CONFIG-VR-10 |	The subject of this property MUST be the version resource URI
CONFIG-VR-11 |	Each resource SHOULD have one instance of the dcterms:modified property
CONFIG-VR-12 |	Tags on versioned resources SHOULD be modifiable even if the resource is otherwise immutable (checked in)
CONFIG-VR-13 |	Configuration Management servers SHOULD indicate the owning component for each version resource using either this property, or using the membership relationship from the component LDPC
CONFIG-VR-14 |	All versioned resources SHOULD have this property; where the property is present, this identifier MUST be unique amongst all currently existing versions of the same concept resource. The subject of this property SHOULD be the concept resource URI
CONFIG-VR-16 |	The subject of each instance of this property MUST be the concept resource URI; the object can be a version resource URI, or a concept resource URI (possibly for a non-versioned resource)
CONFIG-VR-17 |	The subject of each instance of this property MUST be the concept resource URI; the object is likely to be a version resource URI
CONFIG-VR-18 |	One of the type properties MUST have the version resource URI as the subject, and MUST have a resource type of oslc_config:VersionResource
CONFIG-VR-19 |	Other types for the concept resource of which this is a version SHOULD use the concept resource URI as the subject
CONFIG-VR-22 |	PUT: Update the state of a specific version resource; this operation MAY succeed by creating a new version, or MAY succeed without creating a new version for servers that offer version resources with mutable state. A PUT operation on a version resource MAY fail, since version resources may be immutable, or have many immutable properties.
CONFIG-VR-25 |	A versioned resource server SHOULD provide delegated user interface dialogs for selection of concept resources. A versioned resource server MAY provide delegated user interface dialogs for selection of version resources, but such selection is typically performed in a configuration context to find the appropriate version.
CONFIG-VR-26 |	A versioned resource server SHOULD implement compact rendering, both for concept resources and version resources. See Compact Rendering for the handling of configuration context in such rendering.
