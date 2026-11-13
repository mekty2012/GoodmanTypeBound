import Goodman.Methods.RootedSOS.CompactS4.Atlas127.Certificate

/-!
# Atlas 127

graph6: `EZEG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Goodman.Examples.Graph127

open Goodman

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 5), (1, 2), (1, 3), (2, 3), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 127
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "EZEG"
  status := .positive
  formalization := .verified

/-- Complete compact SOS proof across all admissible intervals. -/
theorem status : SatisfiesLowerBound graph :=
  Goodman.Methods.RootedSOS.CompactS4.Atlas127.satisfiesLowerBound_127

end Goodman.Examples.Graph127

#print axioms Goodman.Examples.Graph127.status
