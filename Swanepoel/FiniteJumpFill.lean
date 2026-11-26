module
public import Swanepoel.FiniteJumpReconstruction
@[expose] public section

noncomputable section
namespace Swanepoel
open Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

def finiteRightFill {ι : Type*} (height upper : ι→ℝ) (f : ℝ→ℝ) (y : ℝ) : ℝ :=
  if hy : ∃ i,height i=y then upper (Classical.choose hy) else f y

theorem finiteRightFill_off {ι : Type*} (height upper : ι→ℝ) (f : ℝ→ℝ)
    (y : ℝ) (hy : ∀ i,y≠height i) : finiteRightFill height upper f y=f y := by
  rw [finiteRightFill,dite_eq_right (by rintro ⟨i,hi⟩; exact hy i hi.symm)]

theorem finiteRightFill_at {ι : Type*} (height upper : ι→ℝ) (hinj : Function.Injective height)
    (f : ℝ→ℝ) (i : ι) : finiteRightFill height upper f (height i)=upper i := by
  have hi : ∃ j,height j=height i := ⟨i,rfl⟩
  rw [finiteRightFill,dite_eq_left hi]
  exact congrArg upper (hinj (Classical.choose_spec hi))

theorem finite_jump_reconstruction_off {ι : Type*} [Fintype ι]
    (height lower upper : ι→ℝ) (hinj : Function.Injective height) (f : ℝ→ℝ)
    (hoff : ∀ c,(∀ i,c≠height i) → ∀ᶠ y in 𝓝 c,f y=f c)
    (hat : ∀ i,∀ᶠ y in 𝓝 (height i),y≠height i →
      f y=if y<height i then lower i else upper i)
    (a : ℝ) (ha : ∀ i,height i<a) (hfa : f a=0) :
    ∀ y,(∀ i,y≠height i) → f y=finiteJumpSum height (fun i => lower i-upper i) y := by
  let filled := finiteRightFill height upper f
  have hfilledOff (c : ℝ) (hc : ∀ i,c≠height i) :
      ∀ᶠ y in 𝓝 c,filled y=filled c := by
    have havoid : ∀ᶠ y in 𝓝 c,∀ i,y≠height i := by
      apply Filter.eventually_all.mpr
      intro i
      exact (eventually_same_side_of_ne c (height i) (hc i)).mono (fun _ h => h.2)
    filter_upwards [hoff c hc,havoid] with y hy hne
    change finiteRightFill height upper f y=finiteRightFill height upper f c
    rw [finiteRightFill_off height upper f y hne,finiteRightFill_off height upper f c hc,hy]
  have hfilledAt (i : ι) : ∀ᶠ y in 𝓝 (height i),filled y=filled (height i)+
      (if y<height i then lower i-upper i else 0) := by
    have havoid : ∀ᶠ y in 𝓝 (height i),∀ j,j≠i → y≠height j := by
      apply Filter.eventually_all.mpr
      intro j
      by_cases hji : j=i
      · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hji))
      · exact (eventually_same_side_of_ne (height i) (height j)
          (fun h => hji (hinj h).symm)).mono (fun _ h _ => h.2)
    filter_upwards [hat i,havoid] with y hy hne
    change finiteRightFill height upper f y=finiteRightFill height upper f (height i)+_
    rw [finiteRightFill_at height upper hinj f i]
    by_cases heq : y=height i
    · subst y
      rw [finiteRightFill_at height upper hinj f i]
      simp only [lt_self_iff_false,ite_false,add_zero]
    · have hall : ∀ j,y≠height j := by
        intro j
        by_cases hji : j=i
        · simpa only [hji] using heq
        · exact hne j hji
      rw [finiteRightFill_off height upper f y hall,hy heq]
      split_ifs <;> ring
  have hafilled : filled a=0 := by
    change finiteRightFill height upper f a=0
    rw [finiteRightFill_off height upper f a (fun i => ne_of_gt (ha i)),hfa]
  have hrec := finite_jump_reconstruction height (fun i => lower i-upper i) hinj filled
    hfilledOff hfilledAt a (fun i => (ha i).le) hafilled
  intro y hy
  have hh := hrec y
  change finiteRightFill height upper f y=_ at hh
  rwa [finiteRightFill_off height upper f y hy] at hh

end Swanepoel
