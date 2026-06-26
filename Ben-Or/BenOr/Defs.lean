-- Auto-generated from ben_or_ast.lean by ws_lean (Step B).
import BenOr.Prelude

namespace ben_or

inductive Step where
  | S1
  | S2
  | S3
  deriving DecidableEq, Repr, Inhabited

inductive Msg2Kind where
  | D2
  | Q2
  deriving DecidableEq, Repr, Inhabited

structure Msg1 where
  round : Int
  src : Int
  value : Int
  deriving Inhabited

structure Msg2 where
  kind : Msg2Kind
  round : Int
  src : Int
  value : Int
  deriving Inhabited

structure R_round_src where
  round : Int
  src : Int
  deriving Inhabited

structure State where
  N : Int
  T : Int
  F : Int
  CORRECT : Finset Int
  FAULTY : Finset Int
  ROUNDS : Finset Int
  value : Finmap (fun _ : Int => Int)
  decision : Finmap (fun _ : Int => Int)
  round : Finmap (fun _ : Int => Int)
  step : Finmap (fun _ : Int => Step)
  msgs1 : Finmap (fun _ : Int => Finset Msg1)
  msgs2 : Finmap (fun _ : Int => Finset Msg2)
  ghost_trigger : Bool

def Wf (s : State) : Prop :=
  Finmap.keys s.decision = s.CORRECT ∧
    Finmap.keys s.round = s.CORRECT ∧
      Finmap.keys s.step = s.CORRECT ∧ Finmap.keys s.msgs1 = s.ROUNDS ∧ Finmap.keys s.msgs2 = s.ROUNDS

def agreement_inv (s : State) : Prop :=
  ∀ _v0 ∈ s.CORRECT,
    ∀ _v1 ∈ s.CORRECT,
      (Finmap.lookupD _v0 s.decision = -1 ∨ Finmap.lookupD _v1 s.decision = -1) ∨
        Finmap.lookupD _v0 s.decision = Finmap.lookupD _v1 s.decision

def assumptions_hold (s : State) : Prop :=
  s.N > 5 * s.T ∧
    Finset.card s.CORRECT = s.N - s.F ∧
      s.F = Finset.card s.FAULTY ∧ 1 ∈ s.ROUNDS ∧ ¬-1 ∈ insert 0 (insert 1 (∅ : Finset Int))

def decided_example (s : State) : Prop :=
  ∃ _v2 ∈ s.CORRECT, Finmap.lookupD _v2 s.decision ≠ -1

def type_ok (s : State) : Prop :=
  (Finmap.keys s.value = s.CORRECT ∧
      ∀ k0 ∈ s.CORRECT, Finmap.lookupD k0 s.value ∈ insert 0 (insert 1 (∅ : Finset Int))) ∧
    (Finmap.keys s.decision = s.CORRECT ∧
        ∀ k0 ∈ s.CORRECT,
          Finmap.lookupD k0 s.decision ∈ insert 0 (insert 1 (∅ : Finset Int)) ∪ insert (-1) (∅ : Finset Int)) ∧
      (Finmap.keys s.round = s.CORRECT ∧ ∀ k0 ∈ s.CORRECT, Finmap.lookupD k0 s.round ∈ s.ROUNDS) ∧
        (Finmap.keys s.step = s.CORRECT ∧
            ∀ k0 ∈ s.CORRECT,
              Finmap.lookupD k0 s.step ∈ insert Step.S1 (insert Step.S2 (insert Step.S3 (∅ : Finset Step)))) ∧
          (∀ _v46 ∈ s.ROUNDS,
              ∀ _v47 ∈ Finmap.lookupD _v46 s.msgs1,
                Msg1.src _v47 ∈ s.CORRECT ∪ s.FAULTY ∧
                  _v46 = Msg1.round _v47 ∧ Msg1.value _v47 ∈ insert 0 (insert 1 (∅ : Finset Int))) ∧
            ∀ _v48 ∈ s.ROUNDS,
              ∀ _v49 ∈ Finmap.lookupD _v48 s.msgs2,
                Msg2.src _v49 ∈ s.CORRECT ∪ s.FAULTY ∧
                  _v48 = Msg2.round _v49 ∧
                    Msg2.kind _v49 ∈ insert Msg2Kind.D2 (insert Msg2Kind.Q2 (∅ : Finset Msg2Kind)) ∧
                      (Msg2.kind _v49 = Msg2Kind.D2 ∧ Msg2.value _v49 ∈ insert 0 (insert 1 (∅ : Finset Int)) ∨
                        Msg2.kind _v49 = Msg2Kind.Q2 ∧ Msg2.value _v49 = -2)

def init (s : State) : Prop :=
  True ∧
    (∃ (init_value : Finmap (fun _ : Int => Int)),
        (Finmap.keys init_value = s.CORRECT ∧
            ∀ k0 ∈ s.CORRECT, Finmap.lookupD k0 init_value ∈ insert 0 (insert 1 (∅ : Finset Int))) ∧
          s.value = init_value) ∧
      Finmap.keys s.decision = s.CORRECT ∧
        (∀ _v6 ∈ s.CORRECT, Finmap.lookupD _v6 s.decision = -1) ∧
          Finmap.keys s.round = s.CORRECT ∧
            (∀ _v7 ∈ s.CORRECT, Finmap.lookupD _v7 s.round = 1) ∧
              Finmap.keys s.step = s.CORRECT ∧
                (∀ _v8 ∈ s.CORRECT, Finmap.lookupD _v8 s.step = Step.S1) ∧
                  Finmap.keys s.msgs1 = s.ROUNDS ∧
                    (∀ _v9 ∈ s.ROUNDS, Finmap.lookupD _v9 s.msgs1 = (∅ : Finset Msg1)) ∧
                      Finmap.keys s.msgs2 = s.ROUNDS ∧
                        (∀ _v10 ∈ s.ROUNDS, Finmap.lookupD _v10 s.msgs2 = (∅ : Finset Msg2)) ∧ s.ghost_trigger = false

def init_with_faults (s : State) : Prop :=
  True ∧
    ∃ (init_value : Finmap (fun _ : Int => Int)),
      (Finmap.keys init_value = s.CORRECT ∧
          ∀ k0 ∈ s.CORRECT, Finmap.lookupD k0 init_value ∈ insert 0 (insert 1 (∅ : Finset Int))) ∧
        Finset.powerset
              (Finset.image (fun x => Msg1.mk (x).1 ((x).2).1 ((x).2).2)
                (Finset.product s.ROUNDS (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int)))))) ≠
            (∅ : Finset (Finset Msg1)) ∧
          ∃
            f1 ∈
              Finset.powerset
                (Finset.image (fun x => Msg1.mk (x).1 ((x).2).1 ((x).2).2)
                  (Finset.product s.ROUNDS (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int)))))),
            Finset.powerset
                  (Finset.image (fun x => Msg1.mk (x).1 ((x).2).1 ((x).2).2)
                    (Finset.product s.ROUNDS (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int)))))) ≠
                (∅ : Finset (Finset Msg1)) ∧
              ∃
                f2d ∈
                  Finset.powerset
                    (Finset.image (fun x => Msg1.mk (x).1 ((x).2).1 ((x).2).2)
                      (Finset.product s.ROUNDS (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int)))))),
                Finset.powerset
                      (Finset.image (fun x => R_round_src.mk (x).1 (x).2) (Finset.product s.ROUNDS s.FAULTY)) ≠
                    (∅ : Finset (Finset R_round_src)) ∧
                  ∃
                    f2q ∈
                      Finset.powerset
                        (Finset.image (fun x => R_round_src.mk (x).1 (x).2) (Finset.product s.ROUNDS s.FAULTY)),
                    s.value = init_value ∧
                      Finmap.keys s.decision = s.CORRECT ∧
                        (∀ _v11 ∈ s.CORRECT, Finmap.lookupD _v11 s.decision = -1) ∧
                          Finmap.keys s.round = s.CORRECT ∧
                            (∀ _v12 ∈ s.CORRECT, Finmap.lookupD _v12 s.round = 1) ∧
                              Finmap.keys s.step = s.CORRECT ∧
                                (∀ _v13 ∈ s.CORRECT, Finmap.lookupD _v13 s.step = Step.S1) ∧
                                  Finmap.keys s.msgs1 = s.ROUNDS ∧
                                    (∀ rnd ∈ s.ROUNDS,
                                        Finmap.lookupD rnd s.msgs1 = Finset.filter (fun m => rnd = Msg1.round m) f1) ∧
                                      Finmap.keys s.msgs2 = s.ROUNDS ∧
                                        (∀ rnd ∈ s.ROUNDS,
                                            Finmap.lookupD rnd s.msgs2 =
                                              Finset.image
                                                  (fun msg => Msg2.mk Msg2Kind.D2 rnd (Msg1.src msg) (Msg1.value msg))
                                                  (Finset.filter (fun m => rnd = Msg1.round m) f2d) ∪
                                                Finset.image
                                                  (fun msg => Msg2.mk Msg2Kind.Q2 rnd (R_round_src.src msg) (-2))
                                                  (Finset.filter (fun m => rnd = R_round_src.round m) f2q)) ∧
                                          s.ghost_trigger = false

def faulty_step (s s' : State) : Prop :=
  s.ROUNDS ≠ (∅ : Finset Int) ∧
    (∃ r ∈ s.ROUNDS,
        Finset.powerset
              (Finset.image (fun _v43 => Msg1.mk r (_v43).1 (_v43).2)
                (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))) ≠
            (∅ : Finset (Finset Msg1)) ∧
          ∃
            f1 ∈
              Finset.powerset
                (Finset.image (fun _v43 => Msg1.mk r (_v43).1 (_v43).2)
                  (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))),
            Finset.powerset
                  (Finset.image (fun _v44 => Msg2.mk Msg2Kind.D2 r (_v44).1 (_v44).2)
                    (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))) ≠
                (∅ : Finset (Finset Msg2)) ∧
              ∃
                f2d ∈
                  Finset.powerset
                    (Finset.image (fun _v44 => Msg2.mk Msg2Kind.D2 r (_v44).1 (_v44).2)
                      (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))),
                Finset.powerset (Finset.image (fun _v45 => Msg2.mk Msg2Kind.Q2 r _v45 (-2)) s.FAULTY) ≠
                    (∅ : Finset (Finset Msg2)) ∧
                  ∃ f2q ∈ Finset.powerset (Finset.image (fun _v45 => Msg2.mk Msg2Kind.Q2 r _v45 (-2)) s.FAULTY),
                    s'.msgs1 = Finmap.insert r (Finmap.lookupD r s.msgs1 ∪ f1) s.msgs1 ∧
                      s'.msgs2 = Finmap.insert r (Finmap.lookupD r s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2 ∧
                        s'.ghost_trigger = true) ∧
      s'.N = s.N ∧
        s'.T = s.T ∧
          s'.F = s.F ∧
            s'.CORRECT = s.CORRECT ∧
              s'.FAULTY = s.FAULTY ∧
                s'.ROUNDS = s.ROUNDS ∧
                  s'.value = s.value ∧ s'.decision = s.decision ∧ s'.round = s.round ∧ s'.step = s.step

def step1 (rid : Int) (s s' : State) : Prop :=
  (let _cache21 := Finmap.lookupD rid s.round;
    Finmap.lookupD rid s.step = Step.S1 ∧
      s'.msgs1 =
          Finmap.insert _cache21
            (Finmap.lookupD _cache21 s.msgs1 ∪
              insert (Msg1.mk _cache21 rid (Finmap.lookupD rid s.value)) (∅ : Finset Msg1))
            s.msgs1 ∧
        s'.step = Finmap.insert rid Step.S2 s.step ∧ s'.ghost_trigger = false) ∧
    s'.N = s.N ∧
      s'.T = s.T ∧
        s'.F = s.F ∧
          s'.CORRECT = s.CORRECT ∧
            s'.FAULTY = s.FAULTY ∧
              s'.ROUNDS = s.ROUNDS ∧
                s'.value = s.value ∧ s'.decision = s.decision ∧ s'.round = s.round ∧ s'.msgs2 = s.msgs2

def step2 (rid : Int) (s s' : State) : Prop :=
  (let _cache22 := Finmap.lookupD rid s.round;
    Finmap.lookupD rid s.step = Step.S2 ∧
      Finset.powerset (Finmap.lookupD _cache22 s.msgs1) ≠ (∅ : Finset (Finset Msg1)) ∧
        ∃ received ∈ Finset.powerset (Finmap.lookupD _cache22 s.msgs1),
          Finset.card (Finset.filter (fun _v23 => ∃ _v24 ∈ received, _v23 = Msg1.src _v24) (s.CORRECT ∪ s.FAULTY)) ≥
              s.N - s.T ∧
            ((insert 0 (insert 1 (∅ : Finset Int)) ≠ (∅ : Finset Int) ∧
                ∃ v ∈ insert 0 (insert 1 (∅ : Finset Int)),
                  2 *
                        Finset.card
                          (Finset.filter
                            (fun _v26 =>
                              ∃ _v27 ∈ Finset.filter (fun _v25 => v = Msg1.value _v25) received, _v26 = Msg1.src _v27)
                            (s.CORRECT ∪ s.FAULTY)) >
                      s.N + s.T ∧
                    s'.msgs2 =
                        Finmap.insert _cache22
                          (Finmap.lookupD _cache22 s.msgs2 ∪
                            insert (Msg2.mk Msg2Kind.D2 _cache22 rid v) (∅ : Finset Msg2))
                          s.msgs2 ∧
                      s'.step = Finmap.insert rid Step.S3 s.step ∧ s'.ghost_trigger = true) ∨
              (∀ _v28 ∈ insert 0 (insert 1 (∅ : Finset Int)),
                  2 *
                      Finset.card
                        (Finset.filter
                          (fun _v30 =>
                            ∃ _v31 ∈ Finset.filter (fun _v29 => _v28 = Msg1.value _v29) received, _v30 = Msg1.src _v31)
                          (s.CORRECT ∪ s.FAULTY)) ≤
                    s.N + s.T) ∧
                s'.msgs2 =
                    Finmap.insert _cache22
                      (Finmap.lookupD _cache22 s.msgs2 ∪
                        insert (Msg2.mk Msg2Kind.Q2 _cache22 rid (-2)) (∅ : Finset Msg2))
                      s.msgs2 ∧
                  s'.step = Finmap.insert rid Step.S3 s.step ∧ s'.ghost_trigger = true)) ∧
    s'.N = s.N ∧
      s'.T = s.T ∧
        s'.F = s.F ∧
          s'.CORRECT = s.CORRECT ∧
            s'.FAULTY = s.FAULTY ∧
              s'.ROUNDS = s.ROUNDS ∧
                s'.value = s.value ∧ s'.decision = s.decision ∧ s'.round = s.round ∧ s'.msgs1 = s.msgs1

def step3 (rid : Int) (s s' : State) : Prop :=
  (let _cache32 := Finmap.lookupD rid s.round;
    Finmap.lookupD rid s.step = Step.S3 ∧
      Finset.powerset (Finmap.lookupD _cache32 s.msgs2) ≠ (∅ : Finset (Finset Msg2)) ∧
        (∃ received ∈ Finset.powerset (Finmap.lookupD _cache32 s.msgs2),
            Finset.card (Finset.filter (fun _v33 => ∃ _v34 ∈ received, _v33 = Msg2.src _v34) (s.CORRECT ∪ s.FAULTY)) =
                s.N - s.T ∧
              _cache32 + 1 ∈ s.ROUNDS ∧
                ((insert 0 (insert 1 (∅ : Finset Int)) ≠ (∅ : Finset Int) ∧
                    ∃ v ∈ insert 0 (insert 1 (∅ : Finset Int)),
                      let _cache38 :=
                        Finset.card
                          (Finset.filter
                            (fun _v36 =>
                              ∃
                                _v37 ∈
                                  Finset.filter (fun _v35 => Msg2.kind _v35 = Msg2Kind.D2 ∧ v = Msg2.value _v35)
                                    received,
                                _v36 = Msg2.src _v37)
                            (s.CORRECT ∪ s.FAULTY));
                      _cache38 ≥ s.T + 1 ∧
                        s'.value = Finmap.insert rid v s.value ∧
                          (2 * _cache38 > s.N + s.T ∧ s'.decision = Finmap.insert rid v s.decision ∨
                            ¬2 * _cache38 > s.N + s.T ∧ s'.decision = s.decision)) ∨
                  insert 0 (insert 1 (∅ : Finset Int)) ≠ (∅ : Finset Int) ∧
                    (∃ next_v ∈ insert 0 (insert 1 (∅ : Finset Int)),
                        (∀ _v39 ∈ insert 0 (insert 1 (∅ : Finset Int)),
                            Finset.card
                                (Finset.filter
                                  (fun _v41 =>
                                    ∃
                                      _v42 ∈
                                        Finset.filter
                                          (fun _v40 => Msg2.kind _v40 = Msg2Kind.D2 ∧ _v39 = Msg2.value _v40) received,
                                      _v41 = Msg2.src _v42)
                                  (s.CORRECT ∪ s.FAULTY)) <
                              s.T + 1) ∧
                          s'.value = Finmap.insert rid next_v s.value) ∧
                      s'.decision = s.decision)) ∧
          s'.round = Finmap.insert rid (_cache32 + 1) s.round ∧
            s'.step = Finmap.insert rid Step.S1 s.step ∧ s'.ghost_trigger = true) ∧
    s'.N = s.N ∧
      s'.T = s.T ∧
        s'.F = s.F ∧
          s'.CORRECT = s.CORRECT ∧ s'.FAULTY = s.FAULTY ∧ s'.ROUNDS = s.ROUNDS ∧ s'.msgs1 = s.msgs1 ∧ s'.msgs2 = s.msgs2

def step (s s' : State) : Prop :=
  (s.CORRECT ≠ (∅ : Finset Int) ∧ ∃ id ∈ s.CORRECT, step1 id s s' ∨ step2 id s s' ∨ step3 id s s') ∨ faulty_step s s'

def Next (s s' : State) : Prop :=
  step s s'

def IsRun (tr : Nat → State) : Prop :=
  init (tr 0) ∧ ∀ (i : Nat), Next (tr i) (tr (i + 1))

-- TODO (M3+): `min_cov` (kind coverage)
-- TODO (M3+): `state_cov` (kind coverage)

end ben_or
