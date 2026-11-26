module
public import Swanepoel.RetainedAreaDecomposition
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.family_quadratic_of_area_and_local_pentagons {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (harea : ∀ Y : Finset (PlaneFace G),G.IsJoinClosed ht Y →
      5*(G.familyBoundaryEndCount Y : ℤ)≤8*G.familyK Y → G.FamilyAreaComparison ht Y)
    (hpentagon : G.PentagonCrossingEstimate ht)
    (hzero : ∀ F∈G.defectPlaneFaces ht,(G.faceSourcePorts F).card=5 →
      G.familyInternalCrossings ht {F}=0)
    (Y : Finset (PlaneFace G)) (hY : G.IsJoinClosed ht Y) :
    10000*G.familyR ht Y≤2379*(G.familyK Y)^2 := by
  have hAll : ∀ m : ℕ,∀ Z : Finset (PlaneFace G),Z.card=m → G.IsJoinClosed ht Z →
      10000*G.familyR ht Z≤2379*(G.familyK Z)^2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro Z hcard hZ
      by_cases hsmall : 5*(G.familyBoundaryEndCount Z : ℤ)≤8*G.familyK Z
      · exact G.small_boundary_family_quadratic ht hZ hsmall (harea Z hZ hsmall)
      · have hlarge : 8*G.familyK Z<5*(G.familyBoundaryEndCount Z : ℤ) := by omega
        obtain ⟨F,hF,hfive,hports⟩ := G.large_boundary_exists_five_port_boundary_face ht hZ hlarge
        have C := G.five_port_removal_counts ht hZ F hF hfive hports
        have hless : (Z\{F}).card<m := by have := C.defects; omega
        have hrec := ih (Z\{F}).card hless (Z\{F}) rfl C.remainder_closed
        have hKR : G.familyK (Z\{F})=G.familyK Z-3 := by have := C.K; omega
        rw [hKR] at hrec
        have hdisjoint := hzero F (hZ.subset_defects hF) hfive
        have hmixed := hpentagon Z hZ F hF hfive hports
        exact pentagon_quadratic_step (G.familyK Z) (G.familyBoundaryEndCount Z)
          (G.familyR ht Z) (G.familyR ht (Z\{F})) (G.family_K_nonneg ht hZ) hlarge
          (C.loss_bound hdisjoint hmixed) hrec
  exact hAll Y.card Y rfl hY

theorem PennyGraph.family_quadratic_of_local_five_port_geometry {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdefect : G.DefectAreaLowerBound ht) (hpentagon : G.PentagonCrossingEstimate ht)
    (hzero : ∀ F∈G.defectPlaneFaces ht,(G.faceSourcePorts F).card=5 →
      G.familyInternalCrossings ht {F}=0)
    (Y : Finset (PlaneFace G)) (hY : G.IsJoinClosed ht Y) :
    10000*G.familyR ht Y≤2379*(G.familyK Y)^2 :=
  G.family_quadratic_of_area_and_local_pentagons ht
    (fun _ hZ _ => G.family_area_comparison_of_lower_bound ht hc
      (G.retained_area_lower_of_defect_area ht hdefect) hZ)
    hpentagon hzero Y hY

theorem PennyGraph.canonical_quadratic_of_local_five_port_geometry {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdefect : G.DefectAreaLowerBound ht) (hpentagon : G.PentagonCrossingEstimate ht)
    (hzero : ∀ F∈G.defectPlaneFaces ht,(G.faceSourcePorts F).card=5 →
      G.familyInternalCrossings ht {F}=0) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound := by
  have hh := G.family_quadratic_of_local_five_port_geometry ht hc hdefect hpentagon hzero
    (G.defectPlaneFaces ht) (G.joinClosed_all_defects ht)
  change 10000*((G.familyInternalCrossings ht (G.defectPlaneFaces ht) : ℤ)+
    (G.defectPlaneFaces ht).card)≤2379*(G.familyK (G.defectPlaneFaces ht))^2 at hh
  rw [G.familyInternalCrossings_all_defects ht,G.defectPlaneFaces_card ht,G.familyK_all_defects ht] at hh
  exact hh

end Swanepoel
