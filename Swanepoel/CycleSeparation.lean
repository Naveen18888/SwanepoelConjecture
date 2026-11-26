module
public import Swanepoel.EulerAssembly
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.subdrawing_mono {n : ℕ} (G : PennyGraph n)
    {S T : Finset (ContactEdge G)} (hST : S⊆T) : G.subdrawing S⊆G.subdrawing T := by
  rintro z (hp | he)
  · exact Or.inl hp
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
    obtain ⟨heS,hz⟩ := Set.mem_iUnion.mp he
    exact Or.inr (Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨hST heS,hz⟩⟩)

theorem PennyGraph.edgeClearance_antitone {n : ℕ} (G : PennyGraph n)
    {S T : Finset (ContactEdge G)} (hST : S⊆T) (e : ContactEdge G) (t : ℝ) :
    G.edgeClearance T e t≤G.edgeClearance S e t := by
  have hne : (G.subdrawing S).Nonempty := ⟨G.point e.val.1,Or.inl ⟨e.val.1,rfl⟩⟩
  have hd := Metric.infDist_le_infDist_of_subset (G.subdrawing_mono hST) hne
    (x := G.edgePoint e.val.1 e.val.2 t)
  unfold PennyGraph.edgeClearance
  exact div_le_div_of_nonneg_right (min_le_min_left _ (min_le_min_left _ hd)) (by norm_num)

theorem PennyGraph.edgeSidePoint_in_component_of_subset {n : ℕ} (G : PennyGraph n)
    {S T : Finset (ContactEdge G)} (hST : S⊆T) (e : ContactEdge G) (he : e∉T)
    (left : Bool) {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    G.edgeSidePoint T e left t∈connectedComponentIn (G.subdrawing (insert e S))ᶜ
      (G.edgeSidePoint S e left (1/2)) := by
  have heS : e∉S := fun h => he (hST h)
  have hd := G.edgeClearance_antitone hST e t
  have hspec := G.edgeClearance_spec T e he ht0 ht1
  have hu : ‖G.point e.val.2-G.point e.val.1‖=1 := by
    simpa only [← dist_eq_norm] using e.property.2.symm.2
  have hmem := normal_offset_mem_halfBalls _ (G.edgePoint e.val.1 e.val.2 t) hu hspec.1
  have hball : Metric.ball (G.edgePoint e.val.1 e.val.2 t) (2*G.edgeClearance T e t)⊆
      Metric.ball (G.edgePoint e.val.1 e.val.2 t) (2*G.edgeClearance S e t) :=
    Metric.ball_subset_ball (by linarith)
  have hfixed := G.edge_sides_in_fixed_components S e heS ht0 ht1
  cases left
  · exact hfixed.2 ⟨hball hmem.2.1,hmem.2.2⟩
  · exact hfixed.1 ⟨hball hmem.1.1,hmem.1.2⟩

theorem PennyGraph.separateInsertionSides_mono {n : ℕ} (G : PennyGraph n)
    {S T : Finset (ContactEdge G)} (hST : S⊆T) (e : ContactEdge G) (he : e∉T)
    (hsep : ¬G.SameInsertionSides S e) : ¬G.SameInsertionSides T e := by
  intro hsame
  apply hsep
  unfold PennyGraph.SameInsertionSides at hsame ⊢
  have hpL := G.edgeSidePoint_in_component_of_subset hST e he true
    (t := 1/2) (by norm_num) (by norm_num)
  have hpR := G.edgeSidePoint_in_component_of_subset hST e he false
    (t := 1/2) (by norm_num) (by norm_num)
  have hpT := mem_connectedComponentIn
    (G.edgeSidePoint_mem_complement T e he false (t := 1/2) (by norm_num) (by norm_num))
  rw [← hsame] at hpT
  have hcompl : (G.subdrawing (insert e T))ᶜ⊆(G.subdrawing (insert e S))ᶜ :=
    Set.compl_subset_compl.mpr (G.subdrawing_mono (Finset.insert_subset_insert e hST))
  have hpS := connectedComponentIn_mono (G.edgeSidePoint T e true (1/2)) hcompl hpT
  rw [← connectedComponentIn_eq hpL] at hpS
  exact (connectedComponentIn_eq hpS).trans (connectedComponentIn_eq hpR).symm

end Swanepoel
