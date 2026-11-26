module
public import Swanepoel.PolygonIsoperimetryArea
public import Swanepoel.PolygonCompression
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def stepPrefixVertex (p : Plane) (ds : List Plane) (i : ℕ) : Plane := p+(ds.take i).sum

@[simp] theorem stepPrefixVertex_zero (p : Plane) (ds : List Plane) :
    stepPrefixVertex p ds 0 = p := by simp [stepPrefixVertex]

@[simp] theorem stepPrefixVertex_cons (p d : Plane) (ds : List Plane) (i : ℕ) :
    stepPrefixVertex p (d::ds) (i+1) = stepPrefixVertex (p+d) ds i := by
  simp only [stepPrefixVertex, List.take_succ_cons, List.sum_cons]
  abel

theorem stepDoubleArea_eq_fin_sum (p : Plane) (ds : List Plane) :
    stepDoubleArea p ds = ∑ i : Fin ds.length,
      cross2 (stepPrefixVertex p ds i.val) (stepPrefixVertex p ds (i.val+1)) := by
  induction ds generalizing p with
  | nil => simp [stepDoubleArea]
  | cons d ds ih =>
    rw [stepDoubleArea,ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      stepPrefixVertex_zero, stepPrefixVertex_cons]

def stepCyclicVertices (p : Plane) (ds : List Plane) : ZMod ds.length → Plane :=
  fun j => stepPrefixVertex p ds j.val

theorem stepCyclicVertices_next (p : Plane) (ds : List Plane) [NeZero ds.length]
    (hN2 : 2 ≤ ds.length) (hclosed : ds.sum = 0) (j : ZMod ds.length) :
    stepCyclicVertices p ds (j+1) = stepPrefixVertex p ds (j.val+1) := by
  have hone : (1 : ZMod ds.length).val = 1 := ZMod.val_one'' (by omega)
  change stepPrefixVertex p ds (j+1).val = _
  rw [ZMod.val_add,hone]
  by_cases hj : j.val+1 < ds.length
  · rw [Nat.mod_eq_of_lt hj]
  · have hlast : j.val+1 = ds.length := by have := j.val_lt; omega
    rw [hlast,Nat.mod_self,stepPrefixVertex_zero]
    simp [stepPrefixVertex,hclosed]

theorem stepCyclicVertices_difference (p : Plane) (ds : List Plane) [NeZero ds.length]
    (hN2 : 2 ≤ ds.length) (hclosed : ds.sum = 0) (j : ZMod ds.length) :
    stepCyclicVertices p ds (j+1)-stepCyclicVertices p ds j = ds[j.val]'j.val_lt := by
  rw [stepCyclicVertices_next p ds hN2 hclosed j]
  change stepPrefixVertex p ds (j.val+1)-stepPrefixVertex p ds j.val = _
  rw [stepPrefixVertex,stepPrefixVertex,List.sum_take_succ ds j.val j.val_lt]
  abel

theorem zmod_finEquiv_val {N : ℕ} [NeZero N] (i : Fin N) :
    (ZMod.finEquiv N i).val = i.val := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ N => rfl

theorem stepCyclicDoubleArea_eq (p : Plane) (ds : List Plane) [NeZero ds.length]
    (hN2 : 2 ≤ ds.length) (hclosed : ds.sum = 0) :
    cyclicDoubleArea (Equiv.addRight 1) (stepCyclicVertices p ds) = stepDoubleArea p ds := by
  calc
    _ = ∑ j : ZMod ds.length, cross2 (stepPrefixVertex p ds j.val)
        (stepPrefixVertex p ds (j.val+1)) := by
      unfold cyclicDoubleArea
      apply Finset.sum_congr rfl
      intro j _
      rw [show (Equiv.addRight (1 : ZMod ds.length)) j = j+1 by rfl,
        stepCyclicVertices_next p ds hN2 hclosed]
      rfl
    _ = ∑ i : Fin ds.length, cross2 (stepPrefixVertex p ds i.val)
        (stepPrefixVertex p ds (i.val+1)) := by
      exact (Fintype.sum_equiv (ZMod.finEquiv ds.length).toEquiv
        (fun i : Fin ds.length => cross2 (stepPrefixVertex p ds i.val)
          (stepPrefixVertex p ds (i.val+1)))
        (fun j : ZMod ds.length => cross2 (stepPrefixVertex p ds j.val)
          (stepPrefixVertex p ds (j.val+1))) (by
        intro i
        change cross2 (stepPrefixVertex p ds i.val) (stepPrefixVertex p ds (i.val+1)) =
          cross2 (stepPrefixVertex p ds (ZMod.finEquiv ds.length i).val)
            (stepPrefixVertex p ds ((ZMod.finEquiv ds.length i).val+1))
        rw [zmod_finEquiv_val])).symm
    _ = _ := (stepDoubleArea_eq_fin_sum p ds).symm

theorem closed_short_stepDoubleArea_zero (p : Plane) (ds : List Plane)
    (hclosed : ds.sum = 0) (hshort : ds.length ≤ 2) : stepDoubleArea p ds = 0 := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    cases ds with
    | nil =>
      have hd : d = 0 := by simpa using hclosed
      simp [stepDoubleArea,hd,cross2_self]
    | cons e ds =>
      cases ds with
      | nil =>
        have hde : d+e = 0 := by simpa using hclosed
        have he : e = -d := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hde)
        simp [stepDoubleArea,he,cross2]
        ring
      | cons f rest => simp only [List.length_cons] at hshort; omega

theorem closed_unit_step_isoperimetric (p : Plane) (ds : List Plane)
    (hclosed : ds.sum = 0) (hunit : ∀ d ∈ ds, ‖d‖ = 1) :
    |stepDoubleArea p ds/2| ≤ (ds.length : ℝ)^2/(4*Real.pi) := by
  by_cases hN3 : 3 ≤ ds.length
  · let _ : NeZero ds.length := ⟨by omega⟩
    have hvertices : ∀ j : ZMod ds.length,
        ‖stepCyclicVertices p ds (j+1)-stepCyclicVertices p ds j‖ ≤ 1 := by
      intro j
      rw [stepCyclicVertices_difference p ds (by omega) hclosed]
      exact le_of_eq (hunit _ (List.getElem_mem j.val_lt))
    have harea := finite_polygon_unit_isoperimetric hN3 (stepCyclicVertices p ds) hvertices
    rwa [cyclicSignedArea,stepCyclicDoubleArea_eq p ds (by omega) hclosed] at harea
  · rw [closed_short_stepDoubleArea_zero p ds hclosed (by omega),zero_div,abs_zero]
    positivity

theorem closed_zero_or_unit_step_isoperimetric (p : Plane) (ds : List Plane)
    (hclosed : ds.sum = 0) (hsteps : ∀ d ∈ ds, d = 0 ∨ ‖d‖ = 1) :
    |stepDoubleArea p ds/2| ≤ ((nonzeroSteps ds).length : ℝ)^2/(4*Real.pi) := by
  have hsum : (nonzeroSteps ds).sum = 0 := (nonzeroSteps_sum ds).trans hclosed
  have harea := closed_unit_step_isoperimetric p (nonzeroSteps ds) hsum
    (nonzeroSteps_are_unit ds hsteps)
  rwa [stepDoubleArea_nonzeroSteps] at harea

theorem closed_zero_or_unit_step_perimeter_bound (p : Plane) (ds : List Plane)
    (hclosed : ds.sum = 0) (hsteps : ∀ d ∈ ds, d = 0 ∨ ‖d‖ = 1) :
    |stepDoubleArea p ds/2| ≤ (stepLength ds)^2/(4*Real.pi) := by
  rw [zero_or_unit_length_eq_active_count ds hsteps]
  exact closed_zero_or_unit_step_isoperimetric p ds hclosed hsteps

end Swanepoel
