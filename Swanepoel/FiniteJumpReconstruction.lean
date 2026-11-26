module
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic
@[expose] public section

noncomputable section
namespace Swanepoel
open Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

def finiteJumpSum {ι : Type*} [Fintype ι] (height jump : ι→ℝ) (y : ℝ) : ℝ :=
  ∑ i,if y<height i then jump i else 0

theorem eventually_same_side_of_ne (c h : ℝ) (hne : c≠h) :
    ∀ᶠ y in 𝓝 c,(y<h ↔ c<h) ∧ y≠h := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [eventually_lt_nhds h] with y hy
    exact ⟨iff_of_true hy h,ne_of_lt hy⟩
  · filter_upwards [eventually_gt_nhds h] with y hy
    exact ⟨iff_of_false (not_lt_of_ge hy.le) (not_lt_of_ge h.le),ne_of_gt hy⟩

theorem finiteJumpSum_locally_constant_off {ι : Type*} [Fintype ι]
    (height jump : ι→ℝ) (c : ℝ) (hc : ∀ i,c≠height i) :
    ∀ᶠ y in 𝓝 c,finiteJumpSum height jump y=finiteJumpSum height jump c := by
  have hs : ∀ᶠ y in 𝓝 c,∀ i,(y<height i ↔ c<height i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (eventually_same_side_of_ne c (height i) (hc i)).mono (fun _ h => h.1)
  filter_upwards [hs] with y hy
  unfold finiteJumpSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [hy i]

theorem finiteJumpSum_local_jump {ι : Type*} [Fintype ι]
    (height jump : ι→ℝ) (hinj : Function.Injective height) (i : ι) :
    ∀ᶠ y in 𝓝 (height i),finiteJumpSum height jump y=
      finiteJumpSum height jump (height i)+(if y<height i then jump i else 0) := by
  have hs : ∀ᶠ y in 𝓝 (height i),∀ j,j≠i → (y<height j ↔ height i<height j) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j=i
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
    · exact (eventually_same_side_of_ne (height i) (height j)
        (fun h => hji (hinj h).symm)).mono (fun _ h _ => h.1)
  filter_upwards [hs] with y hy
  have hrest : (∑ j∈(Finset.univ.erase i : Finset ι),if y<height j then jump j else 0)=
      ∑ j∈(Finset.univ.erase i : Finset ι),if height i<height j then jump j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hy j (Finset.mem_erase.mp hj).1]
  have h1 := Finset.sum_erase_add (s := (Finset.univ : Finset ι))
    (f := fun j => if y<height j then jump j else 0) (Finset.mem_univ i)
  have h2 := Finset.sum_erase_add (s := (Finset.univ : Finset ι))
    (f := fun j => if height i<height j then jump j else 0) (Finset.mem_univ i)
  simp only [lt_self_iff_false,ite_false,add_zero] at h2
  change _=finiteJumpSum height jump y at h1
  change _=finiteJumpSum height jump (height i) at h2
  rw [← h1,hrest,h2]

theorem finite_jump_reconstruction {ι : Type*} [Fintype ι]
    (height jump : ι→ℝ) (hinj : Function.Injective height) (f : ℝ→ℝ)
    (hoff : ∀ c,(∀ i,c≠height i) → ∀ᶠ y in 𝓝 c,f y=f c)
    (hat : ∀ i,∀ᶠ y in 𝓝 (height i),f y=f (height i)+(if y<height i then jump i else 0))
    (a : ℝ) (ha : ∀ i,height i≤a) (hfa : f a=0) :
    ∀ y,f y=finiteJumpSum height jump y := by
  let d (y : ℝ) := f y-finiteJumpSum height jump y
  have hlocal : IsLocallyConstant d := by
    apply (IsLocallyConstant.iff_eventually_eq d).mpr
    intro c
    by_cases hc : ∃ i,height i=c
    · obtain ⟨i,rfl⟩ := hc
      filter_upwards [hat i,finiteJumpSum_local_jump height jump hinj i] with y hy hs
      dsimp [d]
      rw [hy,hs]
      ring
    · have hne : ∀ i,c≠height i := fun i h => hc ⟨i,h.symm⟩
      filter_upwards [hoff c hne,finiteJumpSum_locally_constant_off height jump c hne] with y hy hs
      dsimp [d]
      rw [hy,hs]
  have hSa : finiteJumpSum height jump a=0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (not_lt_of_ge (ha i))
  intro y
  have hconst := hlocal.apply_eq_of_isPreconnected isPreconnected_univ (x := y) (y := a) trivial trivial
  dsimp [d] at hconst
  rw [hfa,hSa] at hconst
  linarith only [hconst]

end Swanepoel
