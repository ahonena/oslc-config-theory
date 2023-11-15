#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Nov 14 18:00:33 2023

@author: andrei
"""

from z3 import *
from inspect import currentframe, getframeinfo

frameinfo = getframeinfo(currentframe())

print("Line number: ",frameinfo.lineno)


SMTSolver = Solver()


# RDF model that is modeled here, is from
# https://www.w3.org/TR/rdf11-concepts/#section-rdf-graph

# According to the definition these are distinct and distinguishable, even if 
# they have similar looking values

IRI = DeclareSort('IRI')
BlankNode = DeclareSort('BlankNode')
Literal = DeclareSort('Literal')

# We need to resort to uninterpreted functions to define the RDF triplets
# This kind of technique is called "Theory interpretation" or 
# "Model construction" in automated theorem proving
SubjectType = DeclareSort('SubjectType')
blankNodeAsSubject = Function('blankNodeAsSubject', BlankNode, SubjectType)
iriAsSubject = Function('iriAsSubject', IRI, SubjectType)

ObjectType = DeclareSort('ObjectType')
literalAsObject = Function('literalAsObject', Literal, ObjectType)
blankNodeAsObject = Function('blankNodeAsObject', BlankNode, ObjectType)
iriAsObject = Function('iriAsObject', IRI, ObjectType)

x = Const('x', SubjectType)
b = Const('b', BlankNode)
i = Const('i', IRI)

axiom1 = ForAll(x, Or(Exists(b, x == blankNodeAsSubject(b)), 
                      Exists(i, x == iriAsSubject(i))))
axiom2 = ForAll(b, Exists(x, x == blankNodeAsSubject(b)))
axiom3 = ForAll(i, Exists(x, x == iriAsSubject(i)))
SMTSolver.add(axiom1)
SMTSolver.add(axiom2)
SMTSolver.add(axiom3)

print("Line number: ",getframeinfo(currentframe()).lineno)
print (SMTSolver.check())


I = SetSort(IRI)
B = SetSort(BlankNode)
L = SetSort(Literal)

RDFTriple = Datatype('RDFTriple')
RDFTriple.declare('triple', ('subject', SubjectType), ('predicate', IRI), ('object', ObjectType))
#RDFTriple.declare('triple', ('subject', IRI), ('predicate', IRI), ('object', Literal))
RDFTriple = RDFTriple.create()