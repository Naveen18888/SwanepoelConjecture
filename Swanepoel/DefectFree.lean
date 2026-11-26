module
public import Swanepoel.BlockGeometryCounts
public import Swanepoel.Combinatorics
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem triangle_free_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (h3 : ∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a) :
    (H.edgeFinset.card : ℤ)≤N (Fintype.card V) := by
  classical
  have hf : H.CliqueFree 3 := by
    intro S hS
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hS
    exact h3 a b c hab hbc hac.symm
  have hn : H.edgeFinset.card≤Fintype.card V^2/4 := by
    have hnat := (hf.card_edgeFinset_le (r := 2)).trans_eq
      (SimpleGraph.turanNumber_two (n := Fintype.card V))
    simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using hnat
  have hm := (Nat.le_div_iff_mul_le (by decide : 0<4)).mp hn
  unfold N
  apply (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ)<4)).mpr
  exact_mod_cast hm

theorem TrackSystem.internal_eq_induced_edgeCount (D : TrackSystem) (A : Finset D.Track) :
    D.internal A=(D.crossing.induce (A : Set D.Track)).edgeFinset.card := by
  classical
  let S := (A.product A).filter
    (fun p : D.Track × D.Track => p.1<p.2 ∧ D.crossing.Adj p.1 p.2)
  have hmem (p) (hp : p ∈ S) : p.1 ∈ A ∧ p.2 ∈ A := by
    exact Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  let toEdge (p) (hp : p ∈ S) : Sym2 {v : D.Track // v ∈ A} :=
    s(⟨p.1,(hmem p hp).1⟩,⟨p.2,(hmem p hp).2⟩)
  change S.card=(D.crossing.induce (A : Set D.Track)).edgeFinset.card
  refine Finset.card_bij toEdge ?_ ?_ ?_
  · intro p hp
    exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hp).2.2
  · intro p hp q hq he
    have hpl := (Finset.mem_filter.mp hp).2.1
    have hql := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext (congrArg Subtype.val h.1) (congrArg Subtype.val h.2)
    · have h1 := congrArg Subtype.val h.1
      have h2 := congrArg Subtype.val h.2
      change p.1=q.2 at h1
      change p.2=q.1 at h2
      rw [h1,h2] at hpl
      exact False.elim (not_lt_of_ge (le_of_lt hql) hpl)
  · intro z
    refine Sym2.inductionOn z ?_
    intro i j hij
    have ha : D.crossing.Adj i.val j.val := SimpleGraph.mem_edgeFinset.mp hij
    rcases lt_or_gt_of_ne ha.ne with h | h
    · refine ⟨(i.val,j.val),?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨i.property,j.property⟩,h,ha⟩
      · rfl
    · refine ⟨(j.val,i.val),?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨j.property,i.property⟩,h,ha.symm⟩
      · exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)

theorem TrackSystem.internal_mantel_bound (D : TrackSystem) (h3 : D.NoTriple)
    (A : Finset D.Track) : (D.internal A : ℤ)≤N A.card := by
  classical
  have h := triangle_free_edge_bound (D.crossing.induce (A : Set D.Track))
    (fun a b c hab hbc hca => h3 a.val b.val c.val hab hbc hca)
  have hc : Nat.card ↥(A : Set D.Track)=A.card := by
    rw [Finset.coe_sort_coe,Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype A (fun _ => Iff.rfl)
  simp only [← Nat.card_eq_fintype_card] at h
  rw [hc] at h
  rw [D.internal_eq_induced_edgeCount A]
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h

theorem TrackSystem.disjoint_bound_defect_free (D : TrackSystem) (h3 : D.NoTriple)
    (hf : D.defects=0) : D.DisjointBound := by
  classical
  intro A hA hdis
  have hd : _root_.Disjoint A D.terminal := by
    apply Finset.disjoint_left.mpr
    intro u hu hterm
    exact (Finset.mem_sdiff.mp hterm).2 (hA hu)
  have hcap := D.internal_mantel_bound h3 (A ∪ D.terminal)
  have hs : (D.crossings A D.terminal : ℤ)=∑ u ∈ A, (D.s u : ℤ) := by
    simp [TrackSystem.crossings_sum,TrackSystem.s]
  have hcard : ((A ∪ D.terminal).card : ℤ)=(D.p : ℤ)+A.card := by
    rw [Finset.card_union_of_disjoint hd]
    simp only [Nat.cast_add,TrackSystem.p]
    omega
  rw [D.internal_union A D.terminal hd,D.internal_zero_of_disjoint A hdis,hcard] at hcap
  simpa [TrackSystem.r,TrackSystem.K,hf,hs] using hcap

theorem TrackSystem.crossing_pair_bound_defect_free (D : TrackSystem) (h3 : D.NoTriple)
    (hf : D.defects=0) : D.CrossingPairBound := by
  classical
  intro u _ v _ huv
  have hd : _root_.Disjoint (D.terminal.filter (D.crossing.Adj u))
      (D.terminal.filter (D.crossing.Adj v)) := by
    apply Finset.disjoint_left.mpr
    intro w hwU hwV
    exact h3 u v w huv (Finset.mem_filter.mp hwV).2 (Finset.mem_filter.mp hwU).2.symm
  have hc := Finset.card_le_card (Finset.union_subset
    (Finset.filter_subset (D.crossing.Adj u) D.terminal)
    (Finset.filter_subset (D.crossing.Adj v) D.terminal))
  rw [Finset.card_union_of_disjoint hd] at hc
  have hcast : (D.s u : ℤ)+D.s v≤D.p := by exact_mod_cast hc
  simpa [TrackSystem.K,hf] using hcast

theorem geometric_rhombi_bound {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    (Fintype.card (RhombusSet G) : ℤ)≤N (Fintype.card (TrackComponent G)) := by
  classical
  have h := triangle_free_edge_bound (componentGraph G ht) (componentGraph_noTriple G ht)
  rw [rhombus_count_eq_crossings G ht]
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h

theorem geometric_defect_free_upper_bound {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (heuler : (n : ℤ)-G.edgeCount+Fintype.card (RhombusSet G)=1) :
    (G.edgeCount : ℤ)≤extremalValue n := by
  classical
  let C := geometricBlockCounts G ht 0 (by simpa using heuler) (by simp)
  have hq := geometric_rhombi_bound G ht
  have hbound : (C.q : ℤ)+C.f≤N C.x := by
    change (Fintype.card (RhombusSet G) : ℤ)+0≤
      N ((Fintype.card (TrackComponent G) : ℤ)-2*0)
    simpa only [add_zero,mul_zero,sub_zero] using hq
  exact block_bound C hbound

end Swanepoel
