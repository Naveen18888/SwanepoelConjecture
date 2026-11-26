module
public import Swanepoel.L38Calibration
public import Mathlib.GroupTheory.Perm.Cycle.Basic
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem l38_exists_cyclic_arc_sum {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (hc : next.IsCycleOn Set.univ)
    (a b : ι) (f : ι→ℝ) :
    ∃ S : Finset ι, Finset.sum S (fun i : ι => f (next i)-f i)=f b-f a := by
  classical
  have hc' : next.IsCycleOn (↑(Finset.univ : Finset ι) : Set ι) := by simpa using hc
  obtain ⟨k,hk,hkb⟩ := hc'.exists_pow_eq (a := a) (b := b) (by simp) (by simp)
  let S := (Finset.range k).image (fun j => (next^j) a)
  refine ⟨S,?_⟩
  have hinj : Set.InjOn (fun j : ℕ => (next^j) a) (Finset.range k : Set ℕ) := by
    intro j hj l hl heq
    exact hc'.injOn_pow_apply (by simp)
      (lt_trans (Finset.mem_range.mp hj) hk) (lt_trans (Finset.mem_range.mp hl) hk) heq
  change Finset.sum ((Finset.range k).image (fun j => (next^j) a))
    (fun i => f (next i)-f i)=_
  rw [Finset.sum_image (fun j hj l hl heq => hinj hj hl heq)]
  have hstep (j : ℕ) : next ((next^j) a)=(next^(j+1)) a := by
    rw [pow_succ',Equiv.Perm.coe_mul,Function.comp_apply]
  simp_rw [hstep]
  simpa only [pow_zero,Equiv.Perm.coe_one,id_eq,hkb] using
    Finset.sum_range_sub (fun j : ℕ => f ((next^j) a)) k

theorem l38_cyclic_variation_ge_twice_span {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (hc : next.IsCycleOn Set.univ)
    (a b : ι) (f : ι→ℝ) :
    2*(f b-f a)≤∑ i,|f (next i)-f i| := by
  obtain ⟨S,hS⟩ := l38_exists_cyclic_arc_sum next hc a b f
  have hz : (∑ i,(f (next i)-f i))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp next,sub_self]
  simpa only [hS] using closed_variation_ge_twice_subsum
    (fun i => f (next i)-f i) hz S

end Swanepoel
