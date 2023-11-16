#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Nov 14 18:00:33 2023

@author: andrei
"""

from z3 import *
from inspect import currentframe, getframeinfo


class RDFModel:
    def __init__(self):
        self.SMTSolver = Solver()
        self.define_sorts()
        self.define_functions()
        self.add_axioms()
        
    def define_sorts(self):
        self.IRI = DeclareSort('IRI')
        self.BlankNode = DeclareSort('BlankNode')
        self.Literal = DeclareSort('Literal')
        self.SubjectType = DeclareSort('SubjectType')
        self.PredicateType = DeclareSort('PredicateType')
        self.ObjectType = DeclareSort('ObjectType')

    def define_functions(self):
        self.blankNodeAsSubject = Function('blankNodeAsSubject', self.BlankNode, self.SubjectType)
        self.iriAsSubject = Function('iriAsSubject', self.IRI, self.SubjectType)
        self.iriAsPredicate = Function('iriAsPredicate', self.IRI, self.PredicateType)
        self.literalAsObject = Function('literalAsObject', self.Literal, self.ObjectType)
        self.blankNodeAsObject = Function('blankNodeAsObject', self.BlankNode, self.ObjectType)
        self.iriAsObject = Function('iriAsObject', self.IRI, self.ObjectType)

    def add_axioms(self):
        b = Const('b', self.BlankNode)
        i = Const('i', self.IRI)
        l = Const('l', self.Literal)
        x = Const('x', self.SubjectType)
        p = Const('p', self.PredicateType)
        y = Const('y', self.ObjectType)
       
        axiom_subjects_are_blanks_or_iri = ForAll(x, Or(Exists(b, x == self.blankNodeAsSubject(b)), 
                              Exists(i, x == self.iriAsSubject(i))))
        axiom_blanks_can_be_subjects = ForAll(b, Exists(x, x == self.blankNodeAsSubject(b)))
        axiom_iri_can_be_subjects = ForAll(i, Exists(x, x == self.iriAsSubject(i)))
        axiom_iri_can_be_predicates = ForAll(p,  p == self.iriAsPredicate(i))
        axiom_blanks_can_be_objects = ForAll(b, Exists(y, y == self.blankNodeAsObject(b)))
        axiom_iri_can_be_objects = ForAll(i, Exists(y, y == self.iriAsObject(i)))
        axiom_objects_are_iri_or_literals_or_blanks = ForAll(y, Or(Exists(i, y == self.iriAsObject(i)), 
                                                                   Exists(b, y == self.blankNodeAsObject(b)),
                                                                   Exists(l, y == self.literalAsObject(l))))
        
        
        self.SMTSolver.add(axiom_subjects_are_blanks_or_iri)
        self.SMTSolver.add(axiom_blanks_can_be_subjects)
        self.SMTSolver.add(axiom_iri_can_be_subjects)
        self.SMTSolver.add(axiom_iri_can_be_predicates)
        self.SMTSolver.add(axiom_blanks_can_be_objects)
        self.SMTSolver.add(axiom_iri_can_be_objects)
        self.SMTSolver.add(axiom_objects_are_iri_or_literals_or_blanks)
        
    def create_triple_datatype(self):
        self.RDFTriple = Datatype('RDFTriple')
        self.RDFTriple.declare('triple', ('subject', self.SubjectType), ('predicate', self.PredicateType), ('object', self.ObjectType))
        self.RDFTriple = self.RDFTriple.create()
"""       
#print("Line number: ",getframeinfo(currentframe()).lineno)
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

x = Const('x', SubjectType)
b = Const('b', BlankNode)
i = Const('i', IRI)
axiom_subjects_are_blanks_or_iri = ForAll(x, Or(Exists(b, x == blankNodeAsSubject(b)), 
                      Exists(i, x == iriAsSubject(i))))
axiom_blanks_can_be_subjects = ForAll(b, Exists(x, x == blankNodeAsSubject(b)))
axiom_iri_can_be_subjects = ForAll(i, Exists(x, x == iriAsSubject(i)))
SMTSolver.add(axiom_subjects_are_blanks_or_iri)
SMTSolver.add(axiom_blanks_can_be_subjects)
SMTSolver.add(axiom_iri_can_be_subjects)

PredicateType = DeclareSort('PredicateType')
iriAsPredicate = Function('iriAsPredicate', IRI, PredicateType)
p = Const('p', PredicateType)
axiom_predicate = ForAll(p,  p == iriAsPredicate(i))
SMTSolver.add(axiom_predicate)

ObjectType = DeclareSort('ObjectType')
l = Const('l', Literal)
literalAsObject = Function('literalAsObject', Literal, ObjectType)
blankNodeAsObject = Function('blankNodeAsObject', BlankNode, ObjectType)
iriAsObject = Function('iriAsObject', IRI, ObjectType)
y = Const('y', ObjectType)
axiom_blanks_can_be_objects = ForAll(b, Exists(y, y == blankNodeAsObject(b)))
axiom_iri_can_be_objects = ForAll(i, Exists(y, y == iriAsObject(i)))
axiom_objects_are_iri_or_literals_or_blanks = ForAll(y, Or(Exists(i, y == iriAsObject(i)), 
                                                           Exists(b, y == blankNodeAsObject(b)),
                                                           Exists(l, y == literalAsObject(l))))
SMTSolver.add(axiom_blanks_can_be_objects)
SMTSolver.add(axiom_iri_can_be_objects)
SMTSolver.add(axiom_objects_are_iri_or_literals_or_blanks)

#print("Line number: ",getframeinfo(currentframe()).lineno)
print (SMTSolver.check())


RDFTriple = Datatype('RDFTriple')
RDFTriple.declare('triple', ('subject', SubjectType), ('predicate', PredicateType), ('object', ObjectType))
RDFTriple = RDFTriple.create()

#m = SMTSolver.model()
#for d in m.decls():
#    print(f"{d.name()} = {m[d]}")
"""