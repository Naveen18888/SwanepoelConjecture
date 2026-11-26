module
public import Swanepoel.PentagonSectorGeometry
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PositiveSpineChain
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

def pentagonHitCount {s t : OrientedEdge G} : PositiveSpineChain G s t→ℕ
  | .nil _ => 0
  | .cons s d _ h tail =>
      (if ∃ i : Fin 5,cutRhombus (edgeComponent (P.dart i))
        (SpineTransition.rhombus (⟨(s,d),h⟩ : SpineTransition G)) then 1 else 0)+pentagonHitCount tail

def crossedSpokes {s t : OrientedEdge G} : PositiveSpineChain G s t→Finset (Fin 5)
  | .nil _ => ∅
  | .cons s d _ h tail =>
      (Finset.univ.filter (fun i => cutRhombus (edgeComponent (P.dart i))
        (SpineTransition.rhombus (⟨(s,d),h⟩ : SpineTransition G))))∪crossedSpokes tail

theorem sector_walk {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (K : PentagonSpokeLoops G F P) (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y)
    (hne : ∀ i : Fin 5,edgeComponent s≠edgeComponent (P.dart i)) :
    P.SectorWalk (sourceNormal s) (K.vertexSector s.val.1) (K.vertexSector t.val.1) (p.pentagonHitCount P) := by
  revert hne
  induction p with
  | nil s => intro _; exact .nil _
  | cons s d t h tail ih =>
    intro hne
    have hcomp := (positive_path_component (Relation.ReflTransGen.single h)).symm
    have hnd : ∀ i : Fin 5,edgeComponent d≠edgeComponent (P.dart i) := fun i => hcomp ▸ hne i
    have iht := ih hnd
    have hnormal : sourceNormal d=sourceNormal s := by
      unfold sourceNormal
      rw [← h.to_cellStep.vector_eq]
    rw [hnormal] at iht
    let q : SpineTransition G := ⟨(s,d),h⟩
    change P.SectorWalk (sourceNormal s) (K.vertexSector s.val.1) (K.vertexSector t.val.1)
      ((if ∃ i : Fin 5,cutRhombus (edgeComponent (P.dart i)) q.rhombus then 1 else 0)+tail.pentagonHitCount P)
    by_cases hcut : ∃ i : Fin 5,cutRhombus (edgeComponent (P.dart i)) q.rhombus
    · obtain ⟨i,hi⟩ := hcut
      have hcut' : ∃ j : Fin 5,cutRhombus (edgeComponent (P.dart j)) q.rhombus := ⟨i,hi⟩
      have htrans := K.crossing_step_sector_transition ht hY hFY hports i q hi (hne i)
      have hstep : P.SectorStep (sourceNormal s) (K.vertexSector s.val.1) (K.vertexSector d.val.1) := by
        rcases htrans with ⟨hs,hd,hv⟩ | ⟨hs,hd,hv⟩
        · left
          exact ⟨by rw [hs,hd],by rw [hs]; exact hv⟩
        · right
          exact ⟨by rw [hs,hd],by rw [hd]; exact hv⟩
      rw [ite_eq_left hcut',Nat.add_comm]
      exact PentagonFaceBoundary.SectorWalk.cons hstep iht
    · have huncut := K.uncut_step_code_eq ht q (fun i hi => hcut ⟨i,hi⟩)
      have hsector : K.vertexSector s.val.1=K.vertexSector d.val.1 := congrArg K.codeSector huncut
      rw [ite_eq_right hcut,zero_add,hsector]
      exact iht

theorem pentagonHitCount_le_two {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (K : PentagonSpokeLoops G F P) (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y)
    (hne : ∀ i : Fin 5,edgeComponent s≠edgeComponent (P.dart i)) : p.pentagonHitCount P≤2 :=
  (p.sector_walk P K ht hY hFY hports hne).length_le_two P ht (hY.subset_defects hFY) (sourceNormal_norm s)

theorem crossedSpokes_card_le_hitCount {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y)
    (hne : ∀ i : Fin 5,edgeComponent s≠edgeComponent (P.dart i)) :
    (p.crossedSpokes P).card≤p.pentagonHitCount P := by
  have hinj := P.boundary_spoke_component_injective ht hY hFY hports
  revert hne
  induction p with
  | nil s => intro _; simp only [crossedSpokes,pentagonHitCount,Finset.card_empty,le_refl]
  | cons s d t h tail ih =>
    intro hne
    have hcomp := (positive_path_component (Relation.ReflTransGen.single h)).symm
    have iht := ih (fun i => hcomp ▸ hne i)
    let q : SpineTransition G := ⟨(s,d),h⟩
    let A := (Finset.univ : Finset (Fin 5)).filter (fun i => cutRhombus (edgeComponent (P.dart i)) q.rhombus)
    have hA : A.card≤(if ∃ i : Fin 5,cutRhombus (edgeComponent (P.dart i)) q.rhombus then 1 else 0) := by
      by_cases hex : ∃ i : Fin 5,cutRhombus (edgeComponent (P.dart i)) q.rhombus
      · obtain ⟨i,hi⟩ := hex
        rw [ite_eq_left (show ∃ j : Fin 5,cutRhombus (edgeComponent (P.dart j)) q.rhombus from ⟨i,hi⟩)]
        obtain ⟨C,hS,hD,_⟩ := h
        have hAD := q.other_component_eq_cut ht _ hi (hne i) C hS hD
        have hsub : A⊆{i} := by
          intro j hj
          have hJ := q.other_component_eq_cut ht _ (Finset.mem_filter.mp hj).2 (hne j) C hS hD
          exact Finset.mem_singleton.mpr (hinj (hJ.symm.trans hAD))
        simpa only [Finset.card_singleton] using Finset.card_le_card hsub
      · rw [ite_eq_right hex]
        have hzero : A=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact hex ⟨i,(Finset.mem_filter.mp hi).2⟩
        rw [hzero,Finset.card_empty]
    exact (Finset.card_union_le A (tail.crossedSpokes P)).trans (Nat.add_le_add hA iht)

theorem crossedSpokes_card_le_two {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (K : PentagonSpokeLoops G F P) (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hFY : F∈Y)
    (hports : ∀ e∈G.faceSourcePorts F,edgeComponent e∈G.familyBoundaryTrackComponents Y)
    (hne : ∀ i : Fin 5,edgeComponent s≠edgeComponent (P.dart i)) : (p.crossedSpokes P).card≤2 :=
  (p.crossedSpokes_card_le_hitCount P ht hY hFY hports hne).trans
    (p.pentagonHitCount_le_two P K ht hY hFY hports hne)

end PositiveSpineChain
end Swanepoel
