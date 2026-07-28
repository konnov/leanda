import TendermintSingle.Proofs.Inductive

namespace tendermint_single_indinv

set_option maxRecDepth 10000
set_option maxHeartbeats 0

lemma decision_mem_of_ind_type_ok {s : State} (htype : ind_type_ok s)
    {p : Int} (hp : p ∈ s.Corr) :
    Finmap.lookupD p s.decision ∈ s.ValidValues ∪ insert (-1) ∅ :=
  htype.2.2.1.2 p hp

/-- Section D's `LockLemma`: a precommit quorum fixes the value for every
later precommit quorum. -/
lemma lock_lemma {s : State}
    (hmodel : model_assumptions s) (hinv : typed_ind_inv s)
    {ra rb va vb : Int}
    (hra : ra ∈ Finset.Icc 0 s.MaxRound)
    (hrb : rb ∈ Finset.Icc 0 s.MaxRound)
    (hva : va ∈ s.ValidValues) (hvb : vb ∈ s.ValidValues)
    (hrlt : ra < rb)
    (hqa : (pc_set s ra va).card ≥ 2 * s.T + 1)
    (hqb : (pc_set s rb vb).card ≥ 2 * s.T + 1) :
    va = vb := by
  rcases (typed_ind_inv_iff s).mp hinv with ⟨_, hind⟩
  rcases (ind_inv_iff_named s).mp hind with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hprecommit_quorum,
      _, hlock, _⟩
  obtain ⟨c, hcCorr, hcPC⟩ :=
    quorum_has_correct hmodel (vote_senders_subset s _) hqb
  rcases mem_pc_set.mp hcPC with ⟨_, mc, hmc, hmcid, hmcsrc⟩
  have hsent := hprecommit_quorum rb hrb mc hmc (by simpa [hmcsrc] using hcCorr)
  have hpvq : (pv_set s rb vb).card ≥ 2 * s.T + 1 := by
    rcases hsent with hvalid | hnil
    · simpa [pv_set, vote_senders, votes_for, all_replicas, hmcid,
        eq_comm] using hvalid.2
    · have : vb = -1 := by omega
      exact (hmodel.2.2.2.2.2.2.2.2.1 (this ▸ hvb)).elim
  have hblocked := hlock ra hra va hva
  have hblocked' :
      (pc_set s ra va).card < 2 * s.T + 1 ∨
        ∀ r ∈ Finset.filter (fun rr => rr > ra) (Finset.Icc 0 s.MaxRound),
          ∀ v ∈ s.ValidValues \ insert va ∅,
            (pv_set s r v).card < 2 * s.T + 1 := by
    simpa [pc_set, pv_set, vote_senders, votes_for, all_replicas,
      eq_comm] using hblocked
  rcases hblocked' with hsmall | hfuture
  · omega
  · by_contra hne
    have hrbf : rb ∈ Finset.filter (fun rr => rr > ra)
        (Finset.Icc 0 s.MaxRound) := by
      simp [hrb, hrlt]
    have hvbdiff : vb ∈ s.ValidValues \ insert va ∅ := by
      simp [hvb, Ne.symm hne]
    have := hfuture rb hrbf vb hvbdiff
    omega

/-- `TypedIndInv => Agreement`, corresponding to `AgreementThm` in TLAPS. -/
theorem typed_ind_inv_agreement {s : State}
    (hmodel : model_assumptions s) (hinv : typed_ind_inv s) :
    agreement s := by
  rcases (typed_ind_inv_iff s).mp hinv with ⟨htype, hind⟩
  rcases (ind_inv_iff_named s).mp hind with
    ⟨_, _, _, _, hdecided_quorum, hdecided_valid, _, _, _, _, _, _, _, _,
      _, hnoeq, _, _⟩
  unfold agreement
  intro p₁ hp₁ p₂ hp₂
  by_cases hd₁ : Finmap.lookupD p₁ s.decision = -1
  · exact Or.inl (Or.inl hd₁)
  by_cases hd₂ : Finmap.lookupD p₂ s.decision = -1
  · exact Or.inl (Or.inr hd₂)
  right
  have hd₁mem := decision_mem_of_ind_type_ok htype hp₁
  have hd₂mem := decision_mem_of_ind_type_ok htype hp₂
  have hd₁valid : Finmap.lookupD p₁ s.decision ∈ s.ValidValues := by
    simp at hd₁mem
    exact hd₁mem.resolve_left hd₁
  have hd₂valid : Finmap.lookupD p₂ s.decision ∈ s.ValidValues := by
    simp at hd₂mem
    exact hd₂mem.resolve_left hd₂
  have hs₁ : Finmap.lookupD p₁ s.step = Step.DECIDED :=
    (hdecided_valid p₁ hp₁).mpr hd₁valid
  have hs₂ : Finmap.lookupD p₂ s.step = Step.DECIDED :=
    (hdecided_valid p₂ hp₂).mpr hd₂valid
  obtain ⟨r₁, hr₁, hq₁raw⟩ := hdecided_quorum p₁ hp₁ hs₁
  obtain ⟨r₂, hr₂, hq₂raw⟩ := hdecided_quorum p₂ hp₂ hs₂
  have hq₁ : (pc_set s r₁ (Finmap.lookupD p₁ s.decision)).card ≥
      2 * s.T + 1 := by
    simpa [pc_set, vote_senders, votes_for, all_replicas, eq_comm] using hq₁raw
  have hq₂ : (pc_set s r₂ (Finmap.lookupD p₂ s.decision)).card ≥
      2 * s.T + 1 := by
    simpa [pc_set, vote_senders, votes_for, all_replicas, eq_comm] using hq₂raw
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  · exact lock_lemma hmodel hinv hr₁ hr₂ hd₁valid hd₂valid hlt hq₁ hq₂
  · subst r₂
    obtain ⟨c, hcCorr, hc₁, hc₂⟩ :=
      quorums_intersect_in_correct hmodel
        (vote_senders_subset s _) (vote_senders_subset s _) hq₁ hq₂
    rcases mem_pc_set.mp hc₁ with ⟨_, m₁, hm₁, hid₁, hsrc₁⟩
    rcases mem_pc_set.mp hc₂ with ⟨_, m₂, hm₂, hid₂, hsrc₂⟩
    rcases (hnoeq r₁ hr₁).2.2 c hcCorr with ⟨v, _, hvotes⟩
    have hv₁ := hvotes m₁ hm₁ (by omega)
    have hv₂ := hvotes m₂ hm₂ (by omega)
    omega
  · exact (lock_lemma hmodel hinv hr₂ hr₁ hd₂valid hd₁valid hgt hq₂ hq₁).symm

/-- The complete `InitInd`/`NextInd` induction from the TLAPS proof:
every finite position of a generated `IsRun` satisfies the typed invariant,
and the immutable model assumptions remain true. -/
theorem run_preserves_model_and_typed_ind_inv
    {tr : Nat → State}
    (hmodel : model_assumptions (tr 0))
    (hrun : IsRun tr) :
    ∀ i, model_assumptions (tr i) ∧ typed_ind_inv (tr i) := by
  intro i
  induction i with
  | zero =>
      exact ⟨hmodel, typed_ind_inv_init hmodel hrun.1⟩
  | succ i ih =>
      have hnext : Next (tr i) (tr (i + 1)) := hrun.2 i
      have hmodelNext :=
        next_preserves_model_assumptions ih.1 hnext
      have hinvNext := typed_ind_inv_next ih.1 ih.2 hnext
      simpa [Nat.succ_eq_add_one] using
        And.intro hmodelNext hinvNext

/-- The generated Lean counterpart of the TLAPS top-level agreement
theorem for every state in a protocol run. -/
theorem run_agreement {tr : Nat → State}
    (hmodel : model_assumptions (tr 0))
    (hrun : IsRun tr) (i : Nat) :
    agreement (tr i) := by
  rcases run_preserves_model_and_typed_ind_inv hmodel hrun i with
    ⟨hmodelAt, hinvAt⟩
  exact typed_ind_inv_agreement hmodelAt hinvAt

end tendermint_single_indinv
