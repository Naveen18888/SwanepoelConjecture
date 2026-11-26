module
public import Swanepoel.L38HalfPentagonFamilyCounts
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel.TrackSystem
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cut_twice_internal (D : TrackSystem) (A : Finset D.Track) :
    D.crossings A A=2*D.internal A := by
  have hp (u v : D.Track) :
      D.edgeWeight u v+D.edgeWeight v u=if D.crossing.Adj u v then 1 else 0 := by
    by_cases h : u=v
    · subst v
      simp [edgeWeight]
    · exact D.edgeWeight_pair u v h
  have hf : (∑ u∈A,∑ v∈A,D.edgeWeight v u)=D.internal A := by
    rw [Finset.sum_comm]
    exact (D.internal_sum A).symm
  calc
    D.crossings A A=∑ u∈A,∑ v∈A,(D.edgeWeight u v+D.edgeWeight v u) := by
      simp only [D.crossings_sum,Finset.card_eq_sum_ones,Finset.sum_filter,hp]
    _=D.internal A+D.internal A := by
      simp only [Finset.sum_add_distrib]
      rw [← D.internal_sum,hf]
    _=2*D.internal A := by omega

theorem cut_crossings_univ_sum (D : TrackSystem) (A B : Finset D.Track) :
    D.crossings A B=∑ u : D.Track,∑ v : D.Track,
      if u∈A ∧ v∈B ∧ D.crossing.Adj u v then 1 else 0 := by
  symm
  calc
    _=∑ u : D.Track,if u∈A then
        (∑ v : D.Track,if v∈B then (if D.crossing.Adj u v then 1 else 0) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : u∈A <;> simp [hu,ite_and]
    _=D.crossings A B := by
      simp only [Finset.sum_ite_mem_eq,D.crossings_sum,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem cut_internal_allocation (D : TrackSystem) (T A B C : Finset D.Track)
    (hcover : A∪B=T) (hC : C⊆T) (hinter : A∩B⊆C)
    (hind : D.Disjoint C)
    (hsep : ∀ u∈T,∀ v∈T,D.crossing.Adj u v → u∉C → v∉C →
      (u∈A ∧ v∈A) ∨ (u∈B ∧ v∈B)) :
    D.internal T=D.internal A+D.internal B+
      D.crossings (C\A) A+D.crossings (C\B) B := by
  have hpoint (u v : D.Track) :
      (if u∈T ∧ v∈T ∧ D.crossing.Adj u v then 1 else 0)=
      (if u∈A ∧ v∈A ∧ D.crossing.Adj u v then 1 else 0)+
      (if u∈B ∧ v∈B ∧ D.crossing.Adj u v then 1 else 0)+
      (if u∈C\A ∧ v∈A ∧ D.crossing.Adj u v then 1 else 0)+
      (if u∈A ∧ v∈C\A ∧ D.crossing.Adj u v then 1 else 0)+
      (if u∈C\B ∧ v∈B ∧ D.crossing.Adj u v then 1 else 0)+
      (if u∈B ∧ v∈C\B ∧ D.crossing.Adj u v then 1 else 0) := by
    have hcu : u∈C → u∈A ∨ u∈B := fun hu => Finset.mem_union.mp (hcover.symm ▸ hC hu)
    have hcv : v∈C → v∈A ∨ v∈B := fun hv => Finset.mem_union.mp (hcover.symm ▸ hC hv)
    have hiu : u∈A → u∈B → u∈C := fun ha hb => hinter (Finset.mem_inter.mpr ⟨ha,hb⟩)
    have hiv : v∈A → v∈B → v∈C := fun ha hb => hinter (Finset.mem_inter.mpr ⟨ha,hb⟩)
    have htu : u∈T ↔ u∈A ∨ u∈B := by rw [← hcover]; exact Finset.mem_union
    have htv : v∈T ↔ v∈A ∨ v∈B := by rw [← hcover]; exact Finset.mem_union
    by_cases hadj : D.crossing.Adj u v
    · have hn : ¬(u∈C ∧ v∈C) := fun h => hind u h.1 v h.2 hadj
      have hs : u∈T → v∈T → u∉C → v∉C →
          (u∈A ∧ v∈A) ∨ (u∈B ∧ v∈B) := fun hu hv => hsep u hu v hv hadj
      by_cases hua : u∈A <;> by_cases hub : u∈B <;>
        by_cases hva : v∈A <;> by_cases hvb : v∈B <;>
        by_cases huc : u∈C <;> by_cases hvc : v∈C <;>
        simp_all [Finset.mem_sdiff]
    · simp [hadj]
  have hsum : D.crossings T T=D.crossings A A+D.crossings B B+
      D.crossings (C\A) A+D.crossings A (C\A)+
      D.crossings (C\B) B+D.crossings B (C\B) := by
    simp only [D.cut_crossings_univ_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => hpoint u v))
  rw [D.cut_twice_internal,D.cut_twice_internal,D.cut_twice_internal,
    D.l38_crossings_comm A (C\A),D.l38_crossings_comm B (C\B)] at hsum
  omega

end Swanepoel.TrackSystem
