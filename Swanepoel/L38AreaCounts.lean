module
public import Swanepoel.L38AreaWeights
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.l38BothMass {n : ℕ} (G : PennyGraph n) (A : Finset (TrackComponent G)) : ℝ :=
  ∑ R : RhombusSet G,if edgeComponent R.representative.edgeAB∈A ∧
    edgeComponent R.representative.edgeAD∈A then 1 else 0

theorem PennyGraph.l38BothMass_eq_card {n : ℕ} (G : PennyGraph n) (A : Finset (TrackComponent G)) :
    G.l38BothMass A=(G.retainedRhombi A).card := by
  have h : (∑ R∈G.retainedRhombi A,(1:ℝ))=(G.retainedRhombi A).card := by simp
  rw [PennyGraph.retainedRhombi,Finset.sum_filter] at h
  exact h

theorem PennyGraph.l38BothMass_family {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) : G.l38BothMass (G.familyTrackComponents Y)=G.familyInternalCrossings ht Y := by
  rw [G.l38BothMass_eq_card,G.retained_family_rhombi_card ht]

theorem PennyGraph.l38RhombusMass_counts {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    G.l38RhombusMass Y Z=(G.familyInternalCrossings ht Y : ℝ)+
      (G.familyInternalCrossings ht Z : ℝ)/4+(G.interFamilyCrossings ht Y Z : ℝ)/2 := by
  let A := G.familyTrackComponents Y
  let B := G.familyTrackComponents Z
  have hAB : Disjoint A B := G.familyTrackComponents_disjoint ht hY hZ hYZ
  have hpoint (u v : TrackComponent G) : G.l38TrackWeight Y Z u*G.l38TrackWeight Y Z v=
      (1/2:ℝ)*(if u∈A∪B ∧ v∈A∪B then 1 else 0)+
      (1/2:ℝ)*(if u∈A ∧ v∈A then 1 else 0)-
      (1/4:ℝ)*(if u∈B ∧ v∈B then 1 else 0) := by
    have hu : ¬(u∈A ∧ u∈B) := fun h => Finset.disjoint_left.mp hAB h.1 h.2
    have hv : ¬(v∈A ∧ v∈B) := fun h => Finset.disjoint_left.mp hAB h.1 h.2
    change ((if u∈A then 1 else 0)+(if u∈B then 1/2 else 0))*
      ((if v∈A then 1 else 0)+(if v∈B then 1/2 else 0))=_
    by_cases hua : u∈A <;> by_cases hub : u∈B <;>
      by_cases hva : v∈A <;> by_cases hvb : v∈B <;>
      simp_all only [Finset.mem_union,and_self,not_true_eq_false,and_false,
        or_true,or_false,and_true,ite_true,ite_false] <;> norm_num
  have hexp : G.l38RhombusMass Y Z=(1/2:ℝ)*G.l38BothMass (A∪B)+
      (1/2:ℝ)*G.l38BothMass A-(1/4:ℝ)*G.l38BothMass B := by
    unfold l38RhombusMass l38BothMass
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun R _ => hpoint _ _)
  have hunion : A∪B=G.familyTrackComponents (Y∪Z) := (G.familyTrackComponents_union Y Z).symm
  rw [hexp,hunion,G.l38BothMass_family ht]
  change (1/2:ℝ)*(G.familyInternalCrossings ht (Y∪Z) : ℝ)+
    (1/2:ℝ)*G.l38BothMass (G.familyTrackComponents Y)-
    (1/4:ℝ)*G.l38BothMass (G.familyTrackComponents Z)=_
  rw [G.l38BothMass_family ht,G.l38BothMass_family ht,
    G.family_internal_crossings_union ht hY hZ hYZ]
  push_cast
  ring

theorem PennyGraph.l38_defect_indicator_sum {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (A : Finset (PlaneFace G)) (hA : A⊆G.defectPlaneFaces ht) (a : ℝ) :
    (∑ F∈G.defectPlaneFaces ht,if F∈A then a else 0)=a*A.card := by
  rw [← Finset.sum_filter]
  have hfilter : (G.defectPlaneFaces ht).filter (fun F => F∈A)=A := by
    ext F
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hA h,h⟩⟩
  rw [hfilter]
  simp [mul_comm]

theorem PennyGraph.l38DefectMass_counts {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    G.l38DefectMass ht Y Z=(Y.card : ℝ)+(Z.card : ℝ)/4 := by
  have hpoint (F : PlaneFace G) : (G.l38FaceWeight Y Z F)^2=
      (if F∈Y then (1:ℝ) else 0)+(if F∈Z then (1/4:ℝ) else 0) := by
    have hdis : ¬(F∈Y ∧ F∈Z) := fun h => Finset.disjoint_left.mp hYZ h.1 h.2
    unfold l38FaceWeight
    by_cases hFY : F∈Y <;> by_cases hFZ : F∈Z <;> simp_all; norm_num
  unfold l38DefectMass
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib,G.l38_defect_indicator_sum ht Y hY.subset_defects,
    G.l38_defect_indicator_sum ht Z hZ.subset_defects]
  ring

theorem PennyGraph.l38_area_count_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z)
    (hYZ : Disjoint Y Z) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e) :
    Real.sqrt 3/2*((G.familyInternalCrossings ht Y : ℝ)+Y.card+
      ((G.familyInternalCrossings ht Z : ℝ)+Z.card)/4+(G.interFamilyCrossings ht Y Z : ℝ)/2)≤
      ∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F) := by
  have h := G.l38_weighted_area_lower ht hdegree hY hZ P hP
  rw [G.l38RhombusMass_counts ht hY hZ hYZ,G.l38DefectMass_counts ht hY hZ hYZ] at h
  convert h using 1; ring

theorem PennyGraph.exists_l38_area_count_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z)
    (hYZ : Disjoint Y Z) :
    ∃ P : Fin n→Plane,(∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e) ∧
      Real.sqrt 3/2*((G.familyInternalCrossings ht Y : ℝ)+Y.card+
        ((G.familyInternalCrossings ht Z : ℝ)+Z.card)/4+(G.interFamilyCrossings ht Y Z : ℝ)/2)≤
        ∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F) := by
  obtain ⟨P,hP⟩ := G.exists_l38_weighted_potential ht hc hY hZ
  exact ⟨P,hP,G.l38_area_count_lower ht hdegree hY hZ hYZ P hP⟩

end Swanepoel
