module
public import Swanepoel.RhombusFaces
@[expose] public section

noncomputable section
namespace Swanepoel
namespace RhombusCell
variable {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)

theorem cellPoint_mem_closure_openRegion (ht : G.TriangleFree) {r s : ℝ}
    (hr0 : 0≤r) (hr1 : r≤1) (hs0 : 0≤s) (hs1 : s≤1) :
    C.cellPoint r s∈closure C.openRegion := by
  let f (t : ℝ) := C.cellPoint ((1-t)*r+t/2) ((1-t)*s+t/2)
  have hf : Continuous f := C.continuous_cellPoint.comp
    ((((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.div_const 2)).prodMk
      (((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.div_const 2)))
  have h0 : (0 : ℝ)∈closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]
    exact ⟨le_refl _,by norm_num⟩
  have hmaps : Set.MapsTo f (Set.Ioo (0 : ℝ) 1) C.openRegion := by
    rintro t ⟨ht0,ht1⟩
    have hparam (x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) :
        0<(1-t)*x+t/2 ∧ (1-t)*x+t/2<1 := by
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) hx0]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hx1)]
    exact C.cellPoint_mem_openRegion ht (hparam r hr0 hr1).1 (hparam r hr0 hr1).2
      (hparam s hs0 hs1).1 (hparam s hs0 hs1).2
  have h := map_mem_closure hf h0 hmaps
  simpa only [f,sub_zero,one_mul,zero_div,add_zero] using h

theorem closure_openRegion_eq (ht : G.TriangleFree) : closure C.openRegion=C.closedRegion := by
  apply Set.Subset.antisymm C.closure_openRegion_subset
  rintro z ⟨hr0,hr1,hs0,hs1⟩
  have hz := C.cellPoint_mem_closure_openRegion ht hr0 hr1 hs0 hs1
  rwa [C.reconstruct ht z] at hz

theorem frontier_openRegion_eq_boundary (ht : G.TriangleFree) : frontier C.openRegion=C.boundary := by
  rw [frontier,C.closure_openRegion_eq ht,C.isOpen_openRegion.interior_eq]
  ext z
  constructor
  · rintro ⟨hz,hno⟩
    exact (C.closedRegion_subset_open_union_boundary ht hz).resolve_left hno
  · intro hz
    exact ⟨(C.boundary_coordinates ht hz).1,
      fun ho => Set.disjoint_left.mp (C.boundary_disjoint_openRegion ht) hz ho⟩

theorem corners_eq_of_openRegion_eq (ht : G.TriangleFree) (D : RhombusCell G)
    (h : C.openRegion=D.openRegion) : C.corners=D.corners := by
  have hsub (C D : RhombusCell G) (h : C.openRegion=D.openRegion) : C.corners⊆D.corners := by
    intro i hi
    have hc : G.point i∈closure C.openRegion := by
      rw [C.closure_openRegion_eq ht]
      exact (C.boundary_coordinates ht (C.point_corner_mem_boundary i hi)).1
    rw [h] at hc
    exact D.vertex_mem_corners_of_mem_closedRegion ht i (D.closure_openRegion_subset hc)
  exact Finset.Subset.antisymm (hsub C D h) (hsub D C h.symm)

end RhombusCell

def rhombusFaceMap {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (R : RhombusSet G) : BoundedFace G :=
  ⟨R.representative.openRegion,R.representative.isBoundedFace ht⟩

theorem rhombusFaceMap_injective {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Function.Injective (rhombusFaceMap G ht) := by
  intro R S h
  have hc := R.representative.corners_eq_of_openRegion_eq ht S.representative (congrArg Subtype.val h)
  exact Subtype.ext (R.representative_corners.symm.trans (hc.trans S.representative_corners))

abbrev RhombicFace {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) := Set.range (rhombusFaceMap G ht)

noncomputable instance {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : Fintype (RhombicFace G ht) :=
  (Set.finite_range (rhombusFaceMap G ht)).fintype

theorem rhombic_face_count {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Fintype.card (RhombicFace G ht)=Fintype.card (RhombusSet G) :=
  (Fintype.card_congr (Equiv.ofInjective (rhombusFaceMap G ht) (rhombusFaceMap_injective G ht))).symm

end Swanepoel
