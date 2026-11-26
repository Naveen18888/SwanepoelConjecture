module
public import Swanepoel.CutCanonicalList
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

structure CutPiece where
  size : ℕ
  graph : PennyGraph size
  triangleFree : graph.TriangleFree
  connected : graph.graph.Connected

namespace CutPiece
def Cut (P : CutPiece) := {c : TrackComponent P.graph // c∈P.graph.admissibleOrdinaryCuts}

def banks (P : CutPiece) (c : P.Cut) : OrdinaryCutBanks P.graph c.val :=
  P.graph.chosenCutBanks P.triangleFree c

def child (P : CutPiece) (c : P.Cut) (side : Bool) : CutPiece where
  size := ((P.banks c).bankVertices side).card
  graph := (P.banks c).halfGraph side
  triangleFree := (P.banks c).halfGraph_triangleFree P.triangleFree side
  connected := (P.banks c).halfGraph_connected P.triangleFree P.connected side

def defects (P : CutPiece) : ℕ := P.graph.faceDefectCount P.triangleFree

def defectRegions (P : CutPiece) : Finset (Set Plane) :=
  (P.graph.defectPlaneFaces P.triangleFree).image Subtype.val

theorem child_size_lt (P : CutPiece) (c : P.Cut) (side : Bool) : (P.child c side).size<P.size :=
  (P.banks c).half_vertex_count_lt P.triangleFree side

theorem child_size_sum (P : CutPiece) (c : P.Cut) :
    (P.child c false).size+(P.child c true).size=P.size :=
  (P.banks c).half_vertex_count_sum

theorem child_defects_sum (P : CutPiece) (c : P.Cut) :
    (P.child c false).defects+(P.child c true).defects=P.defects := by
  have hcut := (Finset.mem_filter.mp c.property).1
  have hl := ((P.banks c).canonicalHalfBankRealization P.triangleFree P.connected hcut false).defects
  have hr := ((P.banks c).canonicalHalfBankRealization P.triangleFree P.connected hcut true).defects
  have h := (P.banks c).bank_defect_count_conservation P.triangleFree
  change (P.child c false).defects=_ at hl
  change (P.child c true).defects=_ at hr
  change _=P.defects at h
  omega

theorem child_defectRegions (P : CutPiece) (c : P.Cut) (side : Bool) :
    (P.child c side).defectRegions=
      ((P.banks c).bankDefectFamily P.triangleFree side).image Subtype.val := by
  let B := P.banks c
  have hcut := (Finset.mem_filter.mp c.property).1
  ext S
  constructor
  · intro hS
    obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨K,hK,rfl⟩ := B.half_defect_bank_face_surjective P.triangleFree P.connected hcut side F hF
    exact Finset.mem_image.mpr ⟨K,hK,rfl⟩
  · intro hS
    obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_image.mpr ⟨B.bankDefectPlaneFace P.triangleFree side F hF,
      B.bankDefectPlaneFace_mem_defects P.triangleFree side F hF,rfl⟩

theorem child_defectRegions_partition (P : CutPiece) (c : P.Cut) :
    Disjoint (P.child c false).defectRegions (P.child c true).defectRegions ∧
    (P.child c false).defectRegions∪(P.child c true).defectRegions=P.defectRegions := by
  rw [P.child_defectRegions c false,P.child_defectRegions c true]
  have h := (P.banks c).bankDefectFamily_partition P.triangleFree
  constructor
  · apply Finset.disjoint_left.mpr
    intro S hL hR
    obtain ⟨F,hF,hFS⟩ := Finset.mem_image.mp hL
    obtain ⟨K,hK,hKS⟩ := Finset.mem_image.mp hR
    have hFK : F=K := Subtype.ext (hFS.trans hKS.symm)
    exact Finset.disjoint_left.mp h.1 (hFK ▸ hF) hK
  · rw [← Finset.image_union,h.2]
    rfl

end CutPiece

inductive CompleteCutTree : CutPiece → Type
  | leaf {P : CutPiece} (stopped : P.graph.admissibleOrdinaryCuts=∅) : CompleteCutTree P
  | node {P : CutPiece} (cut : P.Cut)
      (left : CompleteCutTree (P.child cut false))
      (right : CompleteCutTree (P.child cut true)) : CompleteCutTree P

theorem completeCutTree_exists (P : CutPiece) : Nonempty (CompleteCutTree P) := by
  have h : ∀ k : ℕ,∀ Q : CutPiece,Q.size=k → Nonempty (CompleteCutTree Q) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro Q hsize
      by_cases hs : Q.graph.admissibleOrdinaryCuts=∅
      · exact ⟨.leaf hs⟩
      · obtain ⟨c,hc⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        let cut : Q.Cut := ⟨c,hc⟩
        have hl : (Q.child cut false).size<k := by rw [← hsize]; exact Q.child_size_lt cut false
        have hr : (Q.child cut true).size<k := by rw [← hsize]; exact Q.child_size_lt cut true
        obtain ⟨L⟩ := ih _ hl _ rfl
        obtain ⟨R⟩ := ih _ hr _ rfl
        exact ⟨.node cut L R⟩
  exact h P.size P rfl

namespace CompleteCutTree
abbrev CutNode := Sigma CutPiece.Cut

def nodes {P : CutPiece} : CompleteCutTree P → List CutNode
  | .leaf _ => []
  | .node c L R => ⟨P,c⟩::(L.nodes++R.nodes)

def realizedHalves {P : CutPiece} (t : CompleteCutTree P) : List (CutPiece×HalfSystem) :=
  t.nodes.flatMap (fun N =>
    [(N.1,(N.1.banks N.2).canonicalHalfSystem N.1.triangleFree false),
     (N.1,(N.1.banks N.2).canonicalHalfSystem N.1.triangleFree true)])

theorem realizedHalves_realized {P : CutPiece} (t : CompleteCutTree P)
    (Q : CutPiece) (H : HalfSystem) (hH : (Q,H)∈t.realizedHalves) :
    ∃ c : Q.Cut,∃ side : Bool,H=(Q.banks c).canonicalHalfSystem Q.triangleFree side ∧
      Nonempty (H.BankRealization (Q.banks c) Q.triangleFree side) := by
  simp only [realizedHalves,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hH
  obtain ⟨N,_,h | h⟩ := hH
  · cases h
    exact ⟨N.2,false,rfl,⟨(N.1.banks N.2).canonicalHalfBankRealization
      N.1.triangleFree N.1.connected (Finset.mem_filter.mp N.2.property).1 false⟩⟩
  · cases h
    exact ⟨N.2,true,rfl,⟨(N.1.banks N.2).canonicalHalfBankRealization
      N.1.triangleFree N.1.connected (Finset.mem_filter.mp N.2.property).1 true⟩⟩

def leaves {P : CutPiece} : CompleteCutTree P → List CutPiece
  | .leaf _ => [P]
  | .node _ L R => L.leaves++R.leaves

theorem leaves_stopped {P : CutPiece} (t : CompleteCutTree P) :
    ∀ Q∈t.leaves,Q.graph.admissibleOrdinaryCuts=∅ := by
  induction t with
  | leaf hs => simpa only [leaves,List.mem_singleton,forall_eq] using hs
  | node c L R ihL ihR =>
    intro Q hQ
    rcases List.mem_append.mp hQ with h | h
    · exact ihL Q h
    · exact ihR Q h

theorem leaves_vertex_count {P : CutPiece} (t : CompleteCutTree P) :
    (t.leaves.map CutPiece.size).sum=P.size := by
  induction t with
  | leaf _ => simp [leaves]
  | @node P c L R ihL ihR =>
    simpa only [leaves,List.map_append,List.sum_append,ihL,ihR] using P.child_size_sum c

theorem leaves_defect_count {P : CutPiece} (t : CompleteCutTree P) :
    (t.leaves.map CutPiece.defects).sum=P.defects := by
  induction t with
  | leaf _ => simp [leaves]
  | @node P c L R ihL ihR =>
    simpa only [leaves,List.map_append,List.sum_append,ihL,ihR] using P.child_defects_sum c

theorem leaves_defect_occurrences {P : CutPiece} (t : CompleteCutTree P) (S : Set Plane) :
    (t.leaves.map (fun Q => if S∈Q.defectRegions then 1 else 0)).sum=
      if S∈P.defectRegions then 1 else 0 := by
  induction t with
  | leaf _ => simp [leaves]
  | @node P c L R ihL ihR =>
    simp only [leaves,List.map_append,List.sum_append,ihL,ihR]
    have h := P.child_defectRegions_partition c
    have hu : S∈P.defectRegions ↔
        S∈(P.child c false).defectRegions ∨ S∈(P.child c true).defectRegions := by
      rw [← h.2]
      exact Finset.mem_union
    have hd : ¬(S∈(P.child c false).defectRegions ∧ S∈(P.child c true).defectRegions) :=
      fun hh => Finset.disjoint_left.mp h.1 hh.1 hh.2
    by_cases hl : S∈(P.child c false).defectRegions <;>
      by_cases hr : S∈(P.child c true).defectRegions <;> simp_all

end CompleteCutTree
end Swanepoel
