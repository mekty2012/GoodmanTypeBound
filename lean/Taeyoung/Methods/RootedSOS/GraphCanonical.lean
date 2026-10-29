import Taeyoung.Foundation.Relabeling
import Mathlib.Data.List.GetD

/-!
# Finite-graph codes and relabelling witnesses

Certificate coefficient tables must identify relabelled copies of the same
ordinary graph.  `AdjacencyCode n` is the finite Boolean adjacency matrix on
`Fin n`, and `graphOfCode` decodes it.  `relabelCodeByListFin` relabels a graph
along an explicit vertex list, and `homDensity_relabelCodeByListFin` proves that
decoding the relabelled code preserves the homomorphism density.
-/

namespace Taeyoung.Methods.RootedSOS

open Taeyoung

/-- A finite Boolean adjacency matrix, stored row by row so that the standard
lexicographic list order can be used by the executable canonicalizer. -/
abbrev AdjacencyCode (_n : ℕ) := List (List Bool)

/-- The adjacency code of a labelled graph. -/
def adjacencyCode {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    AdjacencyCode n :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ decide (H.Adj i j)

private def adjacencyCodeEntry {n : ℕ} (c : AdjacencyCode n)
    (i j : Fin n) : Bool :=
  ((c[i.1]?).bind fun row ↦ row[j.1]?).getD false

/-- Decode a Boolean matrix, symmetrizing it and deleting its diagonal. -/
def graphOfCode {n : ℕ} (c : AdjacencyCode n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ adjacencyCodeEntry c i j = true

instance graphOfCode_decidableAdj {n : ℕ} (c : AdjacencyCode n) :
    DecidableRel (graphOfCode c).Adj := by
  unfold graphOfCode
  infer_instance

/-- Encoding and then decoding a simple graph is the identity. -/
theorem graphOfCode_adjacencyCode {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] : graphOfCode (adjacencyCode H) = H := by
  ext i j
  simp [graphOfCode, adjacencyCode, adjacencyCodeEntry, H.adj_comm]
  intro h hij
  subst j
  exact H.loopless.irrefl i h

theorem adjacencyCode_eq_iff {n : ℕ} (H K : SimpleGraph (Fin n))
    [DecidableRel H.Adj] [DecidableRel K.Adj] :
    adjacencyCode H = adjacencyCode K ↔ H = K := by
  constructor
  · intro h
    exact (graphOfCode_adjacencyCode H).symm.trans
      ((congrArg graphOfCode h).trans (graphOfCode_adjacencyCode K))
  · intro h
    subst K
    exact congrArg (fun d : DecidableRel H.Adj ↦ @adjacencyCode n H d)
      (Subsingleton.elim _ _)

/-! ## Explicit relabelling witnesses

Certificate generators already know a concrete vertex permutation.  Reading it
from a short list avoids enumerating permutations inside Lean while retaining a
fully checked density identity. -/

/-- Relabel a finite graph by reading old vertices from a list.  The fallback
keeps the executable definition total; certificate checks separately prove
that the list has the expected length and no duplicates. -/
def relabelCodeByListFin {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (l : List (Fin n)) : AdjacencyCode n :=
  List.ofFn fun i ↦ List.ofFn fun j ↦
    decide (G.Adj (l.getD i.1 i) (l.getD j.1 j))

private theorem list_ofFn_getD_eq_fin {n : ℕ} (l : List (Fin n))
    (hlen : l.length = n) :
    List.ofFn (fun i : Fin n ↦ l.getD i.1 i) = l := by
  apply List.ext_get
  · simp [hlen]
  · intro k hk₁ hk₂
    rw [List.get_ofFn, List.getD_eq_getElem]
    · simp
    · omega

/-- A length-`n`, duplicate-free list is a vertex relabelling, so decoding
its checked adjacency code preserves homomorphism density. -/
theorem homDensity_relabelCodeByListFin
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (l : List (Fin n)) (hlen : l.length = n) (hnodup : l.Nodup)
    (W : Graphon Ω μ) :
    homDensity G W = homDensity (graphOfCode (relabelCodeByListFin G l)) W := by
  let f : Fin n → Fin n := fun i ↦ l.getD i.1 i
  have hlf : List.ofFn f = l := list_ofFn_getD_eq_fin l hlen
  have hfnodup : (List.ofFn f).Nodup := by
    rw [hlf]
    exact hnodup
  have hf : Function.Injective f := List.nodup_ofFn.mp hfnodup
  let e : Fin n ≃ Fin n := Equiv.ofBijective f hf.bijective_of_finite
  have hgraph : graphOfCode (relabelCodeByListFin G l) = G.comap f := by
    change graphOfCode (adjacencyCode (G.comap f)) = G.comap f
    exact graphOfCode_adjacencyCode _
  have he : (e : Fin n → Fin n) = f := rfl
  simpa only [hgraph, he] using
    homDensity_iso W (SimpleGraph.Iso.comap e G).symm

end Taeyoung.Methods.RootedSOS
