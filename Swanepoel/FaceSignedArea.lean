module
public import Swanepoel.RetainedMap
public import Swanepoel.PolygonArea
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.faceSignedArea {n : ℕ} (G : PennyGraph n)
    (P : Fin n→Plane) (F : PlaneFace G) : ℝ :=
  -(∑ e∈G.faceIncidentDarts F,cross2 (P e.val.1) (P e.val.2))/2

theorem PennyGraph.all_darts_cross_sum_zero {n : ℕ} (G : PennyGraph n) (P : Fin n→Plane) :
    (∑ e : OrientedEdge G,cross2 (P e.val.1) (P e.val.2))=0 := by
  have h := Equiv.sum_comp G.edgeReversePermutation (fun e => cross2 (P e.val.1) (P e.val.2))
  change (∑ e : OrientedEdge G,cross2 (P e.val.2) (P e.val.1))=_ at h
  have hswap (e : OrientedEdge G) : cross2 (P e.val.2) (P e.val.1)=
      -cross2 (P e.val.1) (P e.val.2) := by unfold cross2; ring
  simp_rw [hswap] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

theorem PennyGraph.all_face_signed_area_sum {n : ℕ} (G : PennyGraph n)
    [Fintype (PlaneFace G)] (P : Fin n→Plane) :
    (∑ F : PlaneFace G,G.faceSignedArea P F)=0 := by
  have h := Finset.sum_fiberwise_of_maps_to
    (fun e _ => Finset.mem_univ (G.sourceFace e) : ∀ e∈(Finset.univ : Finset (OrientedEdge G)),
      G.sourceFace e∈(Finset.univ : Finset (PlaneFace G)))
    (fun e => cross2 (P e.val.1) (P e.val.2))
  change (∑ F : PlaneFace G,∑ e∈G.faceIncidentDarts F,cross2 (P e.val.1) (P e.val.2))=_ at h
  unfold faceSignedArea
  rw [← Finset.sum_div,Finset.sum_neg_distrib,h,G.all_darts_cross_sum_zero P,neg_zero,zero_div]

theorem PennyGraph.bounded_face_signed_area_sum {n : ℕ} (G : PennyGraph n)
    (P : Fin n→Plane) (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val) :
    (∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F))=
      -G.faceSignedArea P outer := by
  let : Fintype (PlaneFace G) := Fintype.ofFinite _
  obtain ⟨O,hO,hunique⟩ := G.exists_unique_outer_face
  have hOuter : outer=O := hunique outer houter
  have hbounded (F : PlaneFace G) : Bornology.IsBounded F.val ↔ F≠outer := by
    constructor
    · intro hF heq
      exact houter (heq ▸ hF)
    · intro hF
      by_contra hn
      exact hF ((hunique F hn).trans hOuter.symm)
  have hsum : (∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F))=
      ∑ F∈(Finset.univ : Finset (PlaneFace G)).erase outer,G.faceSignedArea P F := by
    refine Finset.sum_bij (fun F _ => G.boundedFaceAsPlane F) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro F _
      exact Finset.mem_erase.mpr ⟨(hbounded _).mp F.property.2,Finset.mem_univ _⟩
    · intro F _ H _ heq
      exact G.boundedFaceAsPlane_injective heq
    · intro F hF
      have hb := (hbounded F).mpr (Finset.mem_erase.mp hF).1
      exact ⟨⟨F.val,F.property,hb⟩,Finset.mem_univ _,rfl⟩
  have hall := G.all_face_signed_area_sum P
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (PlaneFace G)))
    (f := fun F => G.faceSignedArea P F) (Finset.mem_univ outer)
  rw [hsum]
  linarith

theorem PennyGraph.faceSignedArea_eq_of_edge_differences {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (P Q : Fin n→Plane)
    (hPQ : ∀ e∈G.faceIncidentDarts F,P e.val.2-P e.val.1=Q e.val.2-Q e.val.1) :
    G.faceSignedArea P F=G.faceSignedArea Q F := by
  let V (a : Fin n) := P a-Q a
  have hV (e : OrientedEdge G) (he : e∈G.faceIncidentDarts F) : V e.val.2=V e.val.1 := by
    have hh := hPQ e he
    dsimp [V]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hh
  have htel := G.sum_faceBoundaryPredecessor F (fun e => cross2 (V e.val.2) (Q e.val.2))
  simp only [G.faceBoundaryPredecessor_end] at htel
  have hends : (∑ e∈G.faceIncidentDarts F,cross2 (V e.val.2) (Q e.val.2))=
      ∑ e∈G.faceIncidentDarts F,cross2 (V e.val.1) (Q e.val.2) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hV e he]
  rw [hends] at htel
  have hedge (e : OrientedEdge G) (he : e∈G.faceIncidentDarts F) :
      cross2 (P e.val.1) (P e.val.2)=cross2 (Q e.val.1) (Q e.val.2)+
        cross2 (V e.val.1) (Q e.val.2)-cross2 (V e.val.1) (Q e.val.1) := by
    have hA : P e.val.1=Q e.val.1+V e.val.1 := by dsimp [V]; abel
    have hB : P e.val.2=Q e.val.2+V e.val.1 := by rw [← hV e he]; dsimp [V]; abel
    rw [hA,hB,cross2_translate,cross2_sub_right]
    ring
  have hsum : (∑ e∈G.faceIncidentDarts F,cross2 (P e.val.1) (P e.val.2))=
      ∑ e∈G.faceIncidentDarts F,cross2 (Q e.val.1) (Q e.val.2) := by
    calc
      _ = ∑ e∈G.faceIncidentDarts F,(cross2 (Q e.val.1) (Q e.val.2)+
          cross2 (V e.val.1) (Q e.val.2)-cross2 (V e.val.1) (Q e.val.1)) :=
        Finset.sum_congr rfl hedge
      _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,htel]; ring
  simp only [faceSignedArea,hsum]

theorem PennyGraph.retained_selected_defect_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e)
    (F : PlaneFace G) (hFY : F∈Y) : G.faceSignedArea P F=G.faceSignedArea G.point F := by
  apply G.faceSignedArea_eq_of_edge_differences F P G.point
  intro e he
  rw [hP,retainedDisplacement_of_mem _ e
    (G.familyTrackComponents_contains_face_edge ht hY e ((Finset.mem_filter.mp he).2 ▸ hFY))]
  rfl

theorem PennyGraph.retained_unselected_defect_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (hnot : F∉Y) : G.faceSignedArea P F=0 := by
  have hh := G.faceSignedArea_eq_of_edge_differences F P (fun _ => 0) (by
    intro e he
    rw [hP,G.family_displacement_on_unretained_defect ht hY F hF hnot e (Finset.mem_filter.mp he).2]
    simp)
  simpa [faceSignedArea,cross2] using hh

end Swanepoel
