module
public import Swanepoel.L38HalfAreaWeighted
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.l38_displacement_norm {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G)) (e : OrientedEdge G) :
    ‖trackDisplacement (G.l38TrackWeight Y Z) e‖=G.l38TrackWeight Y Z (edgeComponent e) := by
  rw [trackDisplacement,norm_smul,carriedVector_norm,mul_one,Real.norm_eq_abs,
    abs_of_nonneg (G.l38TrackWeight_nonneg Y Z (edgeComponent e))]

theorem PennyGraph.l38_outer_perimeter_eq {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y Z : Finset (PlaneFace G)) (P : Fin n→Plane)
    (hP : ∀ e : OrientedEdge G,P e.val.2-P e.val.1=trackDisplacement (G.l38TrackWeight Y Z) e)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val) :
    (∑ e∈G.faceIncidentDarts outer,‖P e.val.2-P e.val.1‖)=
      (G.familyBoundaryEndCount Y : ℝ)+(G.familyBoundaryEndCount Z : ℝ)/2 := by
  have hfull (A : Finset (PlaneFace G)) :
      (∑ e∈G.faceIncidentDarts outer,if edgeComponent e∈G.familyTrackComponents A then (1:ℝ) else 0)=
        G.familyBoundaryEndCount A := by
    rw [← Finset.sum_filter,G.retained_outer_darts_eq ht A outer houter]
    simp [PennyGraph.familyBoundaryEndCount]
  have hnorm (e : OrientedEdge G) : ‖P e.val.2-P e.val.1‖=
      (if edgeComponent e∈G.familyTrackComponents Y then (1:ℝ) else 0)+
        (if edgeComponent e∈G.familyTrackComponents Z then (1/2:ℝ) else 0) := by
    rw [hP,G.l38_displacement_norm]
    rfl
  have hhalf :
      (∑ e∈G.faceIncidentDarts outer,if edgeComponent e∈G.familyTrackComponents Z then (1/2:ℝ) else 0)=
        (1/2:ℝ)*(G.familyBoundaryEndCount Z : ℝ) := by
    rw [← hfull Z,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> norm_num
  simp_rw [hnorm]
  rw [Finset.sum_add_distrib,hfull Y,hhalf]
  ring

end Swanepoel
