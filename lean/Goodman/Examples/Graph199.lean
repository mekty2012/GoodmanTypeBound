import Goodman.Methods.RootedSOS.CompactS4.Atlas199.Certificate

/-!
# Atlas 199

graph6: `El^g`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Goodman.Examples.Graph199

open Goodman

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 199
  vertexCount := 6
  edgeCount := 11
  chromaticNumber := 4
  graph6 := "El^g"
  status := .positive
  formalization := .verified

/-- Complete compact integer SOS proof, including the graphon interpretation. -/
theorem status : SatisfiesLowerBound graph :=
  Goodman.Methods.RootedSOS.CompactS4.Atlas199.satisfiesLowerBound_199

end Goodman.Examples.Graph199

#print axioms Goodman.Examples.Graph199.status
