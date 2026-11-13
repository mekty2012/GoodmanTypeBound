import Goodman.Methods.RootedSOS.Atlas43

/-!
# Atlas 43: verified exact rooted-SOS certificate

graph6: `Dlc`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The proof runs through `Goodman.Methods.RootedSOS.Atlas43`, a chain of
1,097 modules of `decide +kernel` cells.  Verified sequentially on
2026-09-22: every module compiles, the final theorem uses only the three
standard axioms, about six hours in total, peak 15.4 GiB on one module.  Build
it one module at a time (`lean/tools/verify_catalogue.py`), never with a
parallel `lake build`.
-/

namespace Goodman.Examples.Graph043

open Goodman

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 43
  vertexCount := 5
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "Dlc"
  status := .positive
  formalization := .verified

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph := by
  simpa [graph, Goodman.Methods.RootedSOS.House.houseGraph] using
    Goodman.Methods.RootedSOS.Atlas43.satisfiesLowerBound_house

end Goodman.Examples.Graph043
