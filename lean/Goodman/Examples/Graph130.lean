import Goodman.Methods.RootedSOS.CompactS4.Atlas130.Certificate

/-!
# Atlas 130

graph6: `E{CW`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Goodman.Examples.Graph130

open Goodman

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 130
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "E{CW"
  status := .positive
  formalization := .verified

/-- Complete catalogue bound, with both density intervals checked in Lean. -/
theorem status : SatisfiesLowerBound graph :=
  Goodman.Methods.RootedSOS.CompactS4.Atlas130.satisfiesLowerBound_130

#print axioms status

end Goodman.Examples.Graph130
