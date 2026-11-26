module
public import Swanepoel.QuadraticFamilyInduction
public import Swanepoel.RetainedAreaUpper
public import Swanepoel.RhombusRetainedSignedArea
public import Swanepoel.DefectConeCount
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.RetainedAreaLowerBound {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : Prop :=
  ∀ (Y : Finset (PlaneFace G)), G.IsJoinClosed ht Y → ∀ P : Fin n→Plane,
    (∀ e : OrientedEdge G,P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e) →
    Real.sqrt 3/2*(G.familyR ht Y : ℝ)≤
      ∑ F : BoundedFace G,G.faceSignedArea P (G.boundedFaceAsPlane F)

theorem PennyGraph.family_area_comparison_of_lower_bound {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected) (hlower : G.RetainedAreaLowerBound ht)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) : G.FamilyAreaComparison ht Y := by
  obtain ⟨P,hP,hupper⟩ := G.exists_retained_area_upper ht hY hc
  exact ⟨_,hlower Y hY P hP,hupper⟩

theorem PennyGraph.familyInternalCrossings_all_defects {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) : G.familyInternalCrossings ht (G.defectPlaneFaces ht)=
      (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).r := by
  let E := Fintype.equivFin (TrackComponent G)
  have hterminal : (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).terminal=
      G.terminalTrackComponents.map E.toEmbedding := by
    change (Finset.univ\G.ordinaryTrackComponents.map E.toEmbedding)=
      G.terminalTrackComponents.map E.toEmbedding
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,
      Finset.mem_map_equiv,G.mem_terminalTrackComponents]
  unfold PennyGraph.familyInternalCrossings PennyGraph.familyTrackIndices TrackSystem.r
  rw [G.familyTrackComponents_all_defects ht,hterminal]
  rfl

theorem PennyGraph.canonical_quadratic_bound_of_geometry {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hlower : G.RetainedAreaLowerBound ht) (hpentagon : G.PentagonCrossingEstimate ht) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound := by
  have hh := G.family_quadratic_of_area_and_pentagons ht hdegree
    (fun _ hY _ => G.family_area_comparison_of_lower_bound ht hc hlower hY)
    hpentagon (G.defectPlaneFaces ht) (G.joinClosed_all_defects ht)
  change 10000*((G.familyInternalCrossings ht (G.defectPlaneFaces ht) : ℤ)+
    (G.defectPlaneFaces ht).card)≤2379*(G.familyK (G.defectPlaneFaces ht))^2 at hh
  rw [G.familyInternalCrossings_all_defects ht,G.defectPlaneFaces_card ht,G.familyK_all_defects ht] at hh
  exact hh

end Swanepoel
