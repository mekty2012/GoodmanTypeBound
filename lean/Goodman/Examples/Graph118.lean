import Goodman.Methods.RootedSOS.CompactS4.Atlas118.Certificate

/-! Atlas118. Exact integer Gram matrices, their flag-density interpretation,
the complete interval identity, and coloring counts certify the catalogue bound. -/

namespace Goodman.Examples.Graph118

open Goodman

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (1, 2), (1, 4), (1, 5), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 118
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "Eht?"
  status := .positive
  formalization := .verified

theorem status : SatisfiesLowerBound graph :=
  Goodman.Methods.RootedSOS.CompactS4.Atlas118.satisfiesLowerBound_118

end Goodman.Examples.Graph118

#print axioms Goodman.Examples.Graph118.status
