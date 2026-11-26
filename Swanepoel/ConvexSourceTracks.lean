module
public import Swanepoel.PentagonClockwise
public import Swanepoel.SingleCrossings
public import Swanepoel.TrackSimplicity
public import Swanepoel.DefectPorts
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem SpineCone.cross_difference_pos {u v x : Plane} (hu : ‖u‖=1) (hv : ‖v‖=1)
    (huv : |inner ℝ u v|<1/2) (hx : SpineCone u x) :
    0<cross2 u x-cross2 v x := by
  have hc : 0<cross2 u x := lt_of_le_of_lt (by positivity : 0≤Real.sqrt 3*|inner ℝ u x|) hx
  have hsharp := hx.sharpNormal hu
  by_contra hn
  have hcross : cross2 u x≤cross2 v x := by linarith
  have hsqcross : (cross2 u x)^2≤(cross2 v x)^2 :=
    (sq_le_sq₀ hc.le (hc.le.trans hcross)).mpr hcross
  have hgU := cross2_sq_add_inner_sq u x
  have hgV := cross2_sq_add_inner_sq v x
  rw [hu] at hgU
  rw [hv] at hgV
  have hsq : |inner ℝ v x|^2≤|inner ℝ u x|^2 := by
    rw [sq_abs,sq_abs]
    nlinarith
  have habs : |inner ℝ v x|≤|inner ℝ u x| :=
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp hsq
  have hsharpV : SharpNormal v x := by
    unfold SharpNormal at *
    linarith
  exact no_common_sharpNormal u v x hu hv huv hsharp hsharpV

theorem source_cell_center_cone {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (e : OrientedEdge G) (he : SpineSource e) (C : RhombusCell G)
    (hC : edgeComponent C.edgeAB=edgeComponent e ∨ edgeComponent C.edgeAD=edgeComponent e) :
    SpineCone (carriedVector e) (C.center-edgeCenter e) := by
  obtain ⟨a,b,hab,ha,hcenter,_⟩ := C.spineWitness ht (edgeComponent e) hC
  obtain ⟨s,t,hs,_,hE,hall⟩ := component_spine_iff ht e
  have hse : s=e := source_path_eq he hE.1
  subst s
  have forward (a b : OrientedEdge G) (hab : PositiveCellStep a b)
      (hpath : Relation.ReflTransGen PositiveCellStep e a) (hc : stepCenter a b=C.center) :
      SpineCone (carriedVector e) (C.center-edgeCenter e) := by
    have hweak := positive_path_cone ht hpath
    have hhalf := (hab.displacement_cone ht).smul (by norm_num : (0:ℝ)<1/2)
    rw [← positive_path_vector hpath] at hhalf
    have hcone := hweak.add_strict hhalf
    have heq : (edgeCenter a-edgeCenter e)+(1/2:ℝ) • (edgeCenter b-edgeCenter a)=
        stepCenter a b-edgeCenter e := by
      dsimp [stepCenter,RhombusCell.midpoint2]
      module
    rwa [heq,hc] at hcone
  rcases (hall a).mp ha with h | h
  · exact forward a b hab h.1 hcenter
  · have hrev := (onSpine_reverse_iff.mp h).1
    have hp := spine_prefix_closed ht he hrev hab.reverse
    apply forward (reverseEdge b) (reverseEdge a) hab.reverse hp
    rw [stepCenter_reverse,stepCenter_comm]
    exact hcenter

theorem supported_sources_noncrossing {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (e f : OrientedEdge G) (he : SpineSource e) (hf : SpineSource f)
    (hef : cross2 (carriedVector e) (edgeCenter f-edgeCenter e)≤0)
    (hfe : cross2 (carriedVector f) (edgeCenter e-edgeCenter f)≤0) :
    ¬ComponentCrosses (edgeComponent e) (edgeComponent f) := by
  intro hcross
  have hang := component_crossing_angle ht hcross
  have hlineE := component_sameLine e (edgeComponent e) rfl
  have hlineF := component_sameLine f (edgeComponent f) rfl
  have huv : |inner ℝ (carriedVector e) (carriedVector f)|<1/2 := by
    rw [hlineE.abs_inner_eq hlineF]
    exact hang
  obtain ⟨C,hC⟩ := hcross
  have hCE : edgeComponent C.edgeAB=edgeComponent e ∨ edgeComponent C.edgeAD=edgeComponent e :=
    hC.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  have hCF : edgeComponent C.edgeAB=edgeComponent f ∨ edgeComponent C.edgeAD=edgeComponent f :=
    hC.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
  have hconeE := source_cell_center_cone ht e he C hCE
  have hconeF := source_cell_center_cone ht f hf C hCF
  have hp := hconeE.cross_difference_pos (carriedVector_norm e) (carriedVector_norm f) huv
  have hrev : |inner ℝ (carriedVector f) (carriedVector e)|<1/2 := by simpa only [real_inner_comm] using huv
  have hn := hconeF.cross_difference_pos (carriedVector_norm f) (carriedVector_norm e) hrev
  simp only [cross2_sub_right] at hp hn hef hfe
  linarith

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)
include P

theorem other_side_center_right (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) (i j : Fin 5) :
    let e : OrientedEdge G := ⟨(P.vertex i,P.vertex (i+1)),P.contact i⟩
    let f : OrientedEdge G := ⟨(P.vertex j,P.vertex (j+1)),P.contact j⟩
    cross2 (carriedVector e) (edgeCenter f-edgeCenter e)≤0 := by
  let u := G.point (P.vertex (i+1))-G.point (P.vertex i)
  have hpoint (k : Fin 5) : cross2 u (G.point (P.vertex k)-G.point (P.vertex i))≤0 := by
    by_cases hk : k=i
    · simp [hk,cross2]
    by_cases hk1 : k=i+1
    · simp only [hk1,u,cross2_self,le_refl]
    exact (P.clockwise_edge_support ht hF i k hk hk1).le
  have hmid : (1/2:ℝ) • (G.point (P.vertex j)+G.point (P.vertex (j+1)))-
      (1/2:ℝ) • (G.point (P.vertex i)+G.point (P.vertex (i+1)))=
        (1/2:ℝ) • (G.point (P.vertex j)-G.point (P.vertex i))+
        (1/2:ℝ) • (G.point (P.vertex (j+1))-G.point (P.vertex i))-(1/2:ℝ) • u := by
    dsimp [u]
    module
  change cross2 u ((1/2:ℝ) • (G.point (P.vertex j)+G.point (P.vertex (j+1)))-
    (1/2:ℝ) • (G.point (P.vertex i)+G.point (P.vertex (i+1))))≤0
  rw [hmid,cross2_sub_right,cross2_add_right,cross2_smul_right,cross2_smul_right,
    cross2_smul_right,cross2_self,mul_zero,sub_zero]
  linarith [hpoint j,hpoint (j+1)]

theorem source_tracks_noncrossing (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (e f : OrientedEdge G) (he : e∈G.faceSourcePorts F) (hf : f∈G.faceSourcePorts F) :
    ¬ComponentCrosses (edgeComponent e) (edgeComponent f) := by
  have heSource := (Finset.mem_filter.mp he).2.1
  have hfSource := (Finset.mem_filter.mp hf).2.1
  rw [← P.darts] at he hf
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
  exact supported_sources_noncrossing ht _ _ heSource hfSource
    (P.other_side_center_right ht hF i j) (P.other_side_center_right ht hF j i)

end PentagonFaceBoundary
end Swanepoel
