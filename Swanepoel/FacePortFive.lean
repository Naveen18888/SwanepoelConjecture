module
public import Swanepoel.FacePortFourCycle
public import Swanepoel.FaceSupport
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def RhombusCell.portCoordULinear {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : Plane →ₗ[ℝ] ℝ where
  toFun z := cross2 z C.v / cross2 C.u C.v
  map_add' x y := by rw [cross2_add_left]; ring
  map_smul' r z := by rw [cross2_smul_left]; simp only [RingHom.id_apply, smul_eq_mul]; ring

def RhombusCell.portCoordVLinear {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : Plane →ₗ[ℝ] ℝ where
  toFun z := cross2 C.u z / cross2 C.u C.v
  map_add' x y := by rw [cross2_add_right]; ring
  map_smul' r z := by rw [cross2_smul_right]; simp only [RingHom.id_apply, smul_eq_mul]; ring

theorem RhombusCell.coordU_eq_portCoordULinear_sub {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (z : Plane) :
    C.coordU z = C.portCoordULinear z - C.portCoordULinear (G.point C.a) := by
  simp [RhombusCell.coordU, RhombusCell.portCoordULinear, cross2]
  ring

theorem RhombusCell.coordV_eq_portCoordVLinear_sub {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (z : Plane) :
    C.coordV z = C.portCoordVLinear z - C.portCoordVLinear (G.point C.a) := by
  simp only [RhombusCell.coordV, RhombusCell.portCoordVLinear, LinearMap.coe_mk,
    AddHom.coe_mk, cross2_sub_right]
  ring

theorem RhombusCell.portCoordULinear_ne_zero {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) : C.portCoordULinear ≠ 0 := by
  intro he
  have hu : C.portCoordULinear C.u = 1 := div_self (C.cross_ne_zero ht)
  rw [he] at hu
  norm_num at hu

theorem RhombusCell.portCoordVLinear_ne_zero {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) : C.portCoordVLinear ≠ 0 := by
  intro he
  have hv : C.portCoordVLinear C.v = 1 := div_self (C.cross_ne_zero ht)
  rw [he] at hv
  norm_num at hv

theorem RhombusCell.portCoordULinear_corner_bounds {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (i : Fin n) (hi : i ∈ C.corners) :
    C.portCoordULinear (G.point C.a) ≤ C.portCoordULinear (G.point i) ∧
      C.portCoordULinear (G.point i) ≤ C.portCoordULinear (G.point C.a)+1 := by
  have hc := (C.boundary_coordinates ht (C.point_corner_mem_boundary i hi)).1
  have h0 := hc.1
  have h1 := hc.2.1
  rw [C.coordU_eq_portCoordULinear_sub] at h0 h1
  constructor <;> linarith

theorem RhombusCell.portCoordVLinear_corner_bounds {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (i : Fin n) (hi : i ∈ C.corners) :
    C.portCoordVLinear (G.point C.a) ≤ C.portCoordVLinear (G.point i) ∧
      C.portCoordVLinear (G.point i) ≤ C.portCoordVLinear (G.point C.a)+1 := by
  have hc := (C.boundary_coordinates ht (C.point_corner_mem_boundary i hi)).1
  have h0 := hc.2.2.1
  have h1 := hc.2.2.2
  rw [C.coordV_eq_portCoordVLinear_sub] at h0 h1
  constructor <;> linarith

theorem PennyGraph.IsSubFace.subset_rhombus_closedRegion {n : ℕ} {G : PennyGraph n}
    {S : Finset (ContactEdge G)} {F : Set Plane} (hf : G.IsSubFace S F)
    (ht : G.TriangleFree) (hb : Bornology.IsBounded F) (C : RhombusCell G)
    (hends : ∀ e ∈ S, e.val.1 ∈ C.corners ∧ e.val.2 ∈ C.corners) : F ⊆ C.closedRegion := by
  have hUhi := hf.linear_support hb C.portCoordULinear (C.portCoordULinear_ne_zero ht)
    (C.portCoordULinear (G.point C.a)+1) (fun e he =>
      ⟨(C.portCoordULinear_corner_bounds ht _ (hends e he).1).2,
        (C.portCoordULinear_corner_bounds ht _ (hends e he).2).2⟩)
  have hVhi := hf.linear_support hb C.portCoordVLinear (C.portCoordVLinear_ne_zero ht)
    (C.portCoordVLinear (G.point C.a)+1) (fun e he =>
      ⟨(C.portCoordVLinear_corner_bounds ht _ (hends e he).1).2,
        (C.portCoordVLinear_corner_bounds ht _ (hends e he).2).2⟩)
  have hUlo := hf.linear_support hb (-C.portCoordULinear)
    (neg_ne_zero.mpr (C.portCoordULinear_ne_zero ht)) (-C.portCoordULinear (G.point C.a)) (by
      intro e he
      simp only [LinearMap.neg_apply]
      exact ⟨neg_le_neg (C.portCoordULinear_corner_bounds ht _ (hends e he).1).1,
        neg_le_neg (C.portCoordULinear_corner_bounds ht _ (hends e he).2).1⟩)
  have hVlo := hf.linear_support hb (-C.portCoordVLinear)
    (neg_ne_zero.mpr (C.portCoordVLinear_ne_zero ht)) (-C.portCoordVLinear (G.point C.a)) (by
      intro e he
      simp only [LinearMap.neg_apply]
      exact ⟨neg_le_neg (C.portCoordVLinear_corner_bounds ht _ (hends e he).1).1,
        neg_le_neg (C.portCoordVLinear_corner_bounds ht _ (hends e he).2).1⟩)
  intro z hz
  have hUhi' := hUhi z hz
  have hVhi' := hVhi z hz
  have hUlo' := hUlo z hz
  have hVlo' := hVlo z hz
  simp only [LinearMap.neg_apply] at hUlo' hVlo'
  change 0 ≤ C.coordU z ∧ C.coordU z ≤ 1 ∧ 0 ≤ C.coordV z ∧ C.coordV z ≤ 1
  rw [C.coordU_eq_portCoordULinear_sub, C.coordV_eq_portCoordVLinear_sub]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem PennyGraph.face_eq_rhombus_of_subset_closedRegion {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (C : RhombusCell G)
    (hsub : F.val ⊆ C.closedRegion) : F.val = C.openRegion := by
  have hinside : F.val ⊆ C.openRegion := by
    intro z hz
    apply (C.closedRegion_subset_open_union_boundary ht (hsub hz)).resolve_right
    intro hboundary
    exact G.face_subset_complement F hz (C.boundary_subset_drawing hboundary)
  obtain ⟨x,hx⟩ := F.property.nonempty
  exact (F.property.eq_component hx).trans ((C.isBoundedFace ht).1.eq_component (hinside hx)).symm

theorem PennyGraph.defect_face_ne_rhombus {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht)
    (C : RhombusCell G) : F.val ≠ C.openRegion := by
  intro hC
  obtain ⟨B,hB,hBF⟩ := Finset.mem_image.mp hF
  have hnot := (Finset.mem_sdiff.mp hB).2
  apply hnot
  let R : RhombusSet G := ⟨C.corners, ⟨C,rfl⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨R,Finset.mem_univ _,?_⟩
  apply Subtype.ext
  have hrep := R.representative.openRegion_eq_of_corners ht C R.representative_corners
  exact hrep.trans (hC.symm.trans (congrArg (fun H : PlaneFace G => H.val) hBF).symm)

theorem PennyGraph.defect_source_ports_five_le {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    5 ≤ (G.faceSourcePorts F).card := by
  by_contra hn
  have hsmall : (G.facePortEdges F).card ≤ 4 :=
    (G.facePortEdges_card_le F).trans (by omega)
  obtain ⟨C,hends⟩ := G.four_port_edges_rhombus_endpoints ht F hF hsmall
  have hf := G.defect_face_retained_by_source_edges ht F hF
  have hclosed := hf.subset_rhombus_closedRegion ht (G.defectPlaneFace_isBounded ht hF) C hends
  exact G.defect_face_ne_rhombus ht F hF C
    (G.face_eq_rhombus_of_subset_closedRegion ht F C hclosed)

theorem PennyGraph.five_defects_le_two_terminal_tracks {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) : 5 * G.faceDefectCount ht ≤ 2 * G.terminalTrackComponents.card := by
  have hlo : 5 * (G.defectPlaneFaces ht).card ≤
      ∑ F ∈ G.defectPlaneFaces ht, (G.faceSourcePorts F).card := by
    calc
      _ = ∑ _ ∈ G.defectPlaneFaces ht, 5 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (G.defect_source_ports_five_le ht)
  rw [G.defectPlaneFaces_card ht] at hlo
  exact hlo.trans (G.defect_source_ports_card_le_terminal ht)

theorem PennyGraph.defects_le_twice_canonical_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    (G.faceDefectCount ht : ℤ) ≤
      2 * (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K := by
  have hnat := G.five_defects_le_two_terminal_tracks ht
  have hint : 5 * (G.faceDefectCount ht : ℤ) ≤ 2 * G.terminalTrackComponents.card := by
    exact_mod_cast hnat
  rw [G.componentSystem_K_eq]
  omega

end Swanepoel
