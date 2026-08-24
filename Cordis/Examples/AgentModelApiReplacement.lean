import Cordis.Extended.Orchestration

/-!
# Concrete Agent–Model–API provider replacement

This example instantiates the quiet-only orchestration semantics with an
`Agent → Model → APIProvider` dependency chain and two distinct API provider
identities.
-/

namespace Cordis.Examples.AgentModelApiReplacement

open Cordis

inductive Fiber where
  | agent
  | model
  | apiOld
  | apiNew
  deriving DecidableEq

instance : Fintype Fiber where
  elems := {.agent, .model, .apiOld, .apiNew}
  complete fiber := by cases fiber <;> simp

inductive Key where
  | model
  | api
  deriving DecidableEq

instance : Fintype Key where
  elems := {.model, .api}
  complete key := by cases key <;> simp

def spec : Fiber → Core.Spec Key
  | .agent => { deps := {.model} }
  | .model => { deps := {.api}, provs := {.model} }
  | .apiOld | .apiNew => { provs := {.api} }

def emptyView : Core.View Key Fiber := fun _ => none

def agentView : Core.View Key Fiber
  | .model => some .model
  | .api => none

def modelOldView : Core.View Key Fiber
  | .model => none
  | .api => some .apiOld

def modelNewView : Core.View Key Fiber
  | .model => none
  | .api => some .apiNew

def program (_ : Fiber) : List (Effects.WitnessedEffect Unit) := []

def initialLifecycle : Integrated.State Fiber Key Unit where
  registered := {.agent, .model, .apiOld}
  phase
    | .agent => .active agentView Effects.identityAccumulator
    | .model => .active modelOldView Effects.identityAccumulator
    | .apiOld => .active emptyView Effects.identityAccumulator
    | .apiNew => .inactive
  retired := ∅
  world := ()

def initial : Extended.OrchState Fiber Key Unit where
  lifecycle := initialLifecycle
  everRegistered := {.agent, .model, .apiOld}

def retired : Extended.OrchState Fiber Key Unit :=
  Extended.retireEpoch initial .apiOld

def retiringApi : Integrated.State Fiber Key Unit :=
  retired.lifecycle.setPhase .apiOld
    (.unloading emptyView Effects.identityAccumulator)

def retiringModel : Integrated.State Fiber Key Unit :=
  retiringApi.setPhase .model
    (.unloading modelOldView Effects.identityAccumulator)

def retiringAgent : Integrated.State Fiber Key Unit :=
  retiringModel.setPhase .agent
    (.unloading agentView Effects.identityAccumulator)

def inactiveAgent : Integrated.State Fiber Key Unit :=
  (retiringAgent.setPhase .agent .inactive).setWorld
    (Effects.recover Effects.identityAccumulator retiringAgent.world)

def inactiveModel : Integrated.State Fiber Key Unit :=
  (inactiveAgent.setPhase .model .inactive).setWorld
    (Effects.recover Effects.identityAccumulator inactiveAgent.world)

def normalizedLifecycle : Integrated.State Fiber Key Unit :=
  (inactiveModel.setPhase .apiOld .inactive).setWorld
    (Effects.recover Effects.identityAccumulator inactiveModel.world)

def normalized : Extended.OrchState Fiber Key Unit where
  lifecycle := normalizedLifecycle
  everRegistered := initial.everRegistered

def removed : Extended.OrchState Fiber Key Unit :=
  Extended.removeEpoch normalized .apiOld

def inserted : Extended.OrchState Fiber Key Unit :=
  Extended.insertEpoch removed .apiNew

def reloadingApiNew : Integrated.State Fiber Key Unit :=
  inserted.lifecycle.setPhase .apiNew
    (.reloading emptyView [] Effects.identityAccumulator)

def activeApiNew : Integrated.State Fiber Key Unit :=
  reloadingApiNew.setPhase .apiNew
    (.active emptyView Effects.identityAccumulator)

def reloadingModelNew : Integrated.State Fiber Key Unit :=
  activeApiNew.setPhase .model
    (.reloading modelNewView [] Effects.identityAccumulator)

def activeModelNew : Integrated.State Fiber Key Unit :=
  reloadingModelNew.setPhase .model
    (.active modelNewView Effects.identityAccumulator)

def reloadingAgentNew : Integrated.State Fiber Key Unit :=
  activeModelNew.setPhase .agent
    (.reloading agentView [] Effects.identityAccumulator)

def finalLifecycle : Integrated.State Fiber Key Unit :=
  reloadingAgentNew.setPhase .agent
    (.active agentView Effects.identityAccumulator)

def final : Extended.OrchState Fiber Key Unit where
  lifecycle := finalLifecycle
  everRegistered := insert .apiNew initial.everRegistered

private theorem coreState_ext
    {s t : Core.State Fiber Key}
    (hregistered : s.registered = t.registered)
    (hphase : s.phase = t.phase) (hretired : s.retired = t.retired) : s = t := by
  cases s
  cases t
  simp_all

private theorem integratedState_ext
    {s t : Integrated.State Fiber Key Unit}
    (hregistered : s.registered = t.registered)
    (hphase : s.phase = t.phase) (hretired : s.retired = t.retired)
    (hworld : s.world = t.world) : s = t := by
  cases s
  cases t
  simp_all

private theorem apiProvider_eq_some_old :
    Core.provider spec (Integrated.erase initialLifecycle) .api = some .apiOld := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨emptyView, by simp [initialLifecycle, Integrated.erasePhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, initialLifecycle, spec, Core.active,
        Integrated.erasePhase] at hcandidate ⊢

private theorem modelProvider_eq_some :
    Core.provider spec (Integrated.erase initialLifecycle) .model = some .model := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨modelOldView,
      by simp [initialLifecycle, Integrated.erasePhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, initialLifecycle, spec, Core.active,
        Integrated.erasePhase] at hcandidate ⊢

theorem initial_agent_target :
    Core.targetView spec (Integrated.erase initialLifecycle) .agent =
      some agentView := by
  rw [Core.targetView_eq_some_iff]
  refine ⟨by simp [initialLifecycle], by simp [initialLifecycle], ?_, ?_⟩
  · intro key hkey
    cases key
    · exact ⟨.model, modelProvider_eq_some⟩
    · simp [spec] at hkey
  · funext key
    cases key <;> simp [spec, agentView, modelProvider_eq_some]

theorem initial_model_target :
    Core.targetView spec (Integrated.erase initialLifecycle) .model =
      some modelOldView := by
  rw [Core.targetView_eq_some_iff]
  refine ⟨by simp [initialLifecycle], by simp [initialLifecycle], ?_, ?_⟩
  · intro key hkey
    cases key
    · simp [spec] at hkey
    · exact ⟨.apiOld, apiProvider_eq_some_old⟩
  · funext key
    cases key <;> simp [spec, modelOldView, apiProvider_eq_some_old]

theorem initial_api_target :
    Core.targetView spec (Integrated.erase initialLifecycle) .apiOld =
      some emptyView := by
  rw [Core.targetView_eq_some_iff]
  refine ⟨by simp [initialLifecycle], by simp [initialLifecycle], ?_, ?_⟩
  · intro key hkey
    simp [spec] at hkey
  · funext key
    simp [spec, emptyView]

theorem initial_quiet :
    Core.quiet spec (Integrated.erase initialLifecycle) := by
  intro fiber
  cases fiber
  · simpa [Core.LocallyQuiet, initialLifecycle, Integrated.erasePhase] using
      initial_agent_target
  · simpa [Core.LocallyQuiet, initialLifecycle, Integrated.erasePhase] using
      initial_model_target
  · simpa [Core.LocallyQuiet, initialLifecycle, Integrated.erasePhase] using
      initial_api_target
  · simp [Core.LocallyQuiet, initialLifecycle,
      Core.targetView_eq_none_iff_not_ready, Core.TargetReady,
      Integrated.erasePhase]

theorem retired_api_target_none :
    Core.targetView spec (Integrated.erase retired.lifecycle) .apiOld = none := by
  apply Core.targetView_eq_none_iff_not_ready.mpr
  intro ready
  exact ready.2.1 (by simp [retired, Extended.retireEpoch,
    Extended.retireLifecycle, initial, initialLifecycle])

private theorem api_provider_none_retiringApi :
    Core.provider spec (Integrated.erase retiringApi) .api = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro candidate hcandidate
  have valid := Core.provider_sound hcandidate
  cases candidate <;>
    simp [Core.TargetProviderValid, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle, spec, Core.active,
      Integrated.erasePhase, Integrated.State.setPhase] at valid

theorem retiringApi_model_target_none :
    Core.targetView spec (Integrated.erase retiringApi) .model = none := by
  apply Core.targetView_eq_none_iff_not_ready.mpr
  rintro ⟨_, _, satisfied⟩
  rcases satisfied .api (by simp [spec]) with ⟨candidate, hcandidate⟩
  rw [api_provider_none_retiringApi] at hcandidate
  contradiction

private theorem model_provider_none_retiringModel :
    Core.provider spec (Integrated.erase retiringModel) .model = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro candidate hcandidate
  have valid := Core.provider_sound hcandidate
  cases candidate <;>
    simp [Core.TargetProviderValid, retiringModel, retiringApi, retired,
      Extended.retireEpoch, Extended.retireLifecycle, initial,
      initialLifecycle, spec, Core.active, Integrated.erasePhase,
      Integrated.State.setPhase] at valid

theorem retiringModel_agent_target_none :
    Core.targetView spec (Integrated.erase retiringModel) .agent = none := by
  apply Core.targetView_eq_none_iff_not_ready.mpr
  rintro ⟨_, _, satisfied⟩
  rcases satisfied .model (by simp [spec]) with ⟨candidate, hcandidate⟩
  rw [model_provider_none_retiringModel] at hcandidate
  contradiction

theorem retiringAgent_unloadable :
    Core.unloadable (Integrated.erase retiringAgent) .agent := by
  rintro ⟨consumer, view, key, hview, hbinding⟩
  cases consumer <;> cases key <;>
    simp [retiringAgent, retiringModel, retiringApi, retired,
      Extended.retireEpoch, Extended.retireLifecycle, initial,
      initialLifecycle, Core.committedView, Integrated.erasePhase,
      Integrated.State.setPhase] at hview
  all_goals
    subst view
    simp [agentView, modelOldView, emptyView] at hbinding

theorem inactiveAgent_model_unloadable :
    Core.unloadable (Integrated.erase inactiveAgent) .model := by
  rintro ⟨consumer, view, key, hview, hbinding⟩
  cases consumer <;> cases key <;>
    simp [inactiveAgent, retiringAgent, retiringModel, retiringApi, retired,
      Extended.retireEpoch, Extended.retireLifecycle, initial,
      initialLifecycle, Core.committedView, Integrated.erasePhase,
      Integrated.State.setPhase, Integrated.State.setWorld, Effects.recover,
      Effects.identityAccumulator] at hview
  all_goals
    subst view
    simp [modelOldView, emptyView] at hbinding

theorem inactiveModel_api_unloadable :
    Core.unloadable (Integrated.erase inactiveModel) .apiOld := by
  rintro ⟨consumer, view, key, hview, hbinding⟩
  cases consumer <;> cases key <;>
    simp [inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle, Core.committedView, Integrated.erasePhase,
      Integrated.State.setPhase, Integrated.State.setWorld, Effects.recover,
      Effects.identityAccumulator] at hview
  all_goals
    subst view
    simp [emptyView] at hbinding

/-- Explicit six-step downstream shutdown after retiring `apiOld`. -/
theorem retire_normalization_schedule :
    Relation.ReflTransGen (Integrated.Step spec program)
      retired.lifecycle normalized.lifecycle := by
  apply Relation.ReflTransGen.head
  · exact ⟨.apiOld, Integrated.StepAt.leave rfl retired_api_target_none⟩
  · apply Relation.ReflTransGen.head
    · exact ⟨.model,
        Integrated.StepAt.leave rfl retiringApi_model_target_none⟩
    · apply Relation.ReflTransGen.head
      · exact ⟨.agent,
          Integrated.StepAt.leave rfl retiringModel_agent_target_none⟩
      · apply Relation.ReflTransGen.head
        · exact ⟨.agent,
            Integrated.StepAt.unload rfl retiringAgent_unloadable⟩
        · apply Relation.ReflTransGen.head
          · exact ⟨.model,
              Integrated.StepAt.unload rfl inactiveAgent_model_unloadable⟩
          · apply Relation.ReflTransGen.single
            exact ⟨.apiOld,
              Integrated.StepAt.unload rfl inactiveModel_api_unloadable⟩

private theorem normalized_provider_none (key : Key) :
    Core.provider spec (Integrated.erase normalizedLifecycle) key = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro candidate hcandidate
  have valid := Core.provider_sound hcandidate
  cases candidate <;>
    simp [Core.TargetProviderValid, normalizedLifecycle, inactiveModel,
      inactiveAgent, retiringAgent, retiringModel, retiringApi, retired,
      Extended.retireEpoch, Extended.retireLifecycle, initial,
      initialLifecycle, spec, Core.active, Integrated.erasePhase,
      Integrated.State.setPhase, Integrated.State.setWorld, Effects.recover,
      Effects.identityAccumulator] at valid

theorem normalized_target_none (fiber : Fiber) :
    Core.targetView spec (Integrated.erase normalizedLifecycle) fiber = none := by
  apply Core.targetView_eq_none_iff_not_ready.mpr
  intro ready
  cases fiber with
  | agent =>
      rcases ready.2.2 .model (by simp [spec]) with ⟨candidate, hcandidate⟩
      rw [normalized_provider_none] at hcandidate
      contradiction
  | model =>
      rcases ready.2.2 .api (by simp [spec]) with ⟨candidate, hcandidate⟩
      rw [normalized_provider_none] at hcandidate
      contradiction
  | apiOld =>
      exact ready.2.1 (by simp [normalizedLifecycle, inactiveModel,
        inactiveAgent, retiringAgent, retiringModel, retiringApi, retired,
        Extended.retireEpoch, Extended.retireLifecycle, initial,
        initialLifecycle])
  | apiNew =>
      exact (by simpa [normalizedLifecycle, inactiveModel, inactiveAgent,
        retiringAgent, retiringModel, retiringApi, retired,
        Extended.retireEpoch, Extended.retireLifecycle, initial,
        initialLifecycle] using ready.1)

theorem normalized_quiet :
    Core.quiet spec (Integrated.erase normalizedLifecycle) := by
  intro fiber
  have hphase : (Integrated.erase normalizedLifecycle).phase fiber =
      .inactive := by
    cases fiber <;> simp [normalizedLifecycle, inactiveModel,
      inactiveAgent, retiringAgent, retiringModel, retiringApi, retired,
      Extended.retireEpoch, Extended.retireLifecycle, initial,
      initialLifecycle, Integrated.erasePhase, Integrated.State.setPhase,
      Integrated.State.setWorld, Effects.recover,
      Effects.identityAccumulator]
  unfold Core.LocallyQuiet
  rw [hphase]
  exact normalized_target_none fiber

private theorem removed_provider_none (key : Key) :
    Core.provider spec (Integrated.erase removed.lifecycle) key = none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro candidate hcandidate
  have valid := Core.provider_sound hcandidate
  cases candidate <;>
    simp [Core.TargetProviderValid, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle, spec, Core.active, Integrated.erasePhase,
      Integrated.State.setPhase, Integrated.State.setWorld, Effects.recover,
      Effects.identityAccumulator] at valid

theorem removed_target_none (fiber : Fiber) :
    Core.targetView spec (Integrated.erase removed.lifecycle) fiber = none := by
  apply Core.targetView_eq_none_iff_not_ready.mpr
  intro ready
  cases fiber with
  | agent =>
      rcases ready.2.2 .model (by simp [spec]) with ⟨candidate, hcandidate⟩
      rw [removed_provider_none] at hcandidate
      contradiction
  | model =>
      rcases ready.2.2 .api (by simp [spec]) with ⟨candidate, hcandidate⟩
      rw [removed_provider_none] at hcandidate
      contradiction
  | apiOld | apiNew =>
      simpa [removed, Extended.removeEpoch, Extended.removeLifecycle,
        normalized, normalizedLifecycle, inactiveModel, inactiveAgent,
        retiringAgent, retiringModel, retiringApi, retired,
        Extended.retireEpoch, Extended.retireLifecycle, initial,
        initialLifecycle] using ready.1

theorem removed_quiet :
    Core.quiet spec (Integrated.erase removed.lifecycle) := by
  intro fiber
  have hphase : (Integrated.erase removed.lifecycle).phase fiber =
      .inactive := by
    cases fiber <;> simp [removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle, Integrated.erasePhase,
      Integrated.State.setPhase, Integrated.State.setWorld, Effects.recover,
      Effects.identityAccumulator]
  unfold Core.LocallyQuiet
  rw [hphase]
  exact removed_target_none fiber

private theorem apiNew_target
    (state : Integrated.State Fiber Key Unit)
    (registered : Fiber.apiNew ∈ state.registered)
    (notRetired : Fiber.apiNew ∉ state.retired) :
    Core.targetView spec (Integrated.erase state) .apiNew = some emptyView := by
  rw [Core.targetView_eq_some_iff]
  refine ⟨by simpa using registered, by simpa using notRetired, ?_, ?_⟩
  · intro key hkey
    simp [spec] at hkey
  · funext key
    simp [spec, emptyView]

theorem inserted_api_target :
    Core.targetView spec (Integrated.erase inserted.lifecycle) .apiNew =
      some emptyView := by
  apply apiNew_target
  · simp [inserted, Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · simp [inserted, Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]

theorem reloadingApiNew_target :
    Core.targetView spec (Integrated.erase reloadingApiNew) .apiNew =
      some emptyView := by
  apply apiNew_target
  · simp [reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]
  · simp [reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]

private theorem apiProvider_eq_some_new :
    Core.provider spec (Integrated.erase activeApiNew) .api = some .apiNew := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨emptyView, by simp [activeApiNew, Integrated.erasePhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, activeApiNew, reloadingApiNew, inserted,
        Extended.insertEpoch, Extended.insertLifecycle, removed,
        Extended.removeEpoch, Extended.removeLifecycle, normalized,
        normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
        retiringModel, retiringApi, retired, Extended.retireEpoch,
        Extended.retireLifecycle, initial, initialLifecycle, spec, Core.active,
        Integrated.erasePhase, Integrated.State.setPhase,
        Integrated.State.setWorld, Effects.recover,
        Effects.identityAccumulator] at hcandidate ⊢

private theorem modelNew_target_at
    (state : Integrated.State Fiber Key Unit)
    (registered : Fiber.model ∈ state.registered)
    (notRetired : Fiber.model ∉ state.retired)
    (providerApi : Core.provider spec (Integrated.erase state) .api =
      some .apiNew) :
    Core.targetView spec (Integrated.erase state) .model = some modelNewView := by
  rw [Core.targetView_eq_some_iff]
  refine ⟨by simpa using registered, by simpa using notRetired, ?_, ?_⟩
  · intro key hkey
    cases key
    · simp [spec] at hkey
    · exact ⟨.apiNew, providerApi⟩
  · funext key
    cases key <;> simp [spec, modelNewView, providerApi]

theorem activeApiNew_model_target :
    Core.targetView spec (Integrated.erase activeApiNew) .model =
      some modelNewView := by
  apply modelNew_target_at
  · simp [activeApiNew, reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]
  · simp [activeApiNew, reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]
  · exact apiProvider_eq_some_new

private theorem apiProvider_eq_some_reloadingModel :
    Core.provider spec (Integrated.erase reloadingModelNew) .api = some .apiNew := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [reloadingModelNew, activeApiNew, reloadingApiNew,
      inserted, Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨emptyView, by simp [reloadingModelNew, activeApiNew,
      Integrated.erasePhase, Integrated.State.setPhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, reloadingModelNew, activeApiNew,
        reloadingApiNew, inserted, Extended.insertEpoch,
        Extended.insertLifecycle, removed, Extended.removeEpoch,
        Extended.removeLifecycle, normalized, normalizedLifecycle,
        inactiveModel, inactiveAgent, retiringAgent, retiringModel,
        retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
        initial, initialLifecycle, spec, Core.active, Integrated.erasePhase,
        Integrated.State.setPhase, Integrated.State.setWorld,
        Effects.recover, Effects.identityAccumulator] at hcandidate ⊢

theorem reloadingModelNew_target :
    Core.targetView spec (Integrated.erase reloadingModelNew) .model =
      some modelNewView := by
  apply modelNew_target_at
  · simp [reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · simp [reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · exact apiProvider_eq_some_reloadingModel

private theorem modelProvider_eq_some_finalPrefix :
    Core.provider spec (Integrated.erase activeModelNew) .model = some .model := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [activeModelNew, reloadingModelNew, activeApiNew,
      reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨modelNewView, by simp [activeModelNew, Integrated.erasePhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, activeModelNew, reloadingModelNew,
        activeApiNew, reloadingApiNew, inserted, Extended.insertEpoch,
        Extended.insertLifecycle, removed, Extended.removeEpoch,
        Extended.removeLifecycle, normalized, normalizedLifecycle,
        inactiveModel, inactiveAgent, retiringAgent, retiringModel,
        retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
        initial, initialLifecycle, spec, Core.active, Integrated.erasePhase,
        Integrated.State.setPhase, Integrated.State.setWorld,
        Effects.recover, Effects.identityAccumulator] at hcandidate ⊢

private theorem agent_target_at
    (state : Integrated.State Fiber Key Unit)
    (registered : Fiber.agent ∈ state.registered)
    (notRetired : Fiber.agent ∉ state.retired)
    (providerModel : Core.provider spec (Integrated.erase state) .model =
      some .model) :
    Core.targetView spec (Integrated.erase state) .agent = some agentView := by
  rw [Core.targetView_eq_some_iff]
  refine ⟨by simpa using registered, by simpa using notRetired, ?_, ?_⟩
  · intro key hkey
    cases key
    · exact ⟨.model, providerModel⟩
    · simp [spec] at hkey
  · funext key
    cases key <;> simp [spec, agentView, providerModel]

theorem activeModelNew_agent_target :
    Core.targetView spec (Integrated.erase activeModelNew) .agent =
      some agentView := by
  apply agent_target_at
  · simp [activeModelNew, reloadingModelNew, activeApiNew,
      reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]
  · simp [activeModelNew, reloadingModelNew, activeApiNew,
      reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]
  · exact modelProvider_eq_some_finalPrefix

private theorem modelProvider_eq_some_reloadingAgent :
    Core.provider spec (Integrated.erase reloadingAgentNew) .model = some .model := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [reloadingAgentNew, activeModelNew, reloadingModelNew,
      activeApiNew, reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨modelNewView, by simp [reloadingAgentNew, activeModelNew,
      Integrated.erasePhase, Integrated.State.setPhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, reloadingAgentNew, activeModelNew,
        reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
        Extended.insertEpoch, Extended.insertLifecycle, removed,
        Extended.removeEpoch, Extended.removeLifecycle, normalized,
        normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
        retiringModel, retiringApi, retired, Extended.retireEpoch,
        Extended.retireLifecycle, initial, initialLifecycle, spec, Core.active,
        Integrated.erasePhase, Integrated.State.setPhase,
        Integrated.State.setWorld, Effects.recover,
        Effects.identityAccumulator] at hcandidate ⊢

theorem reloadingAgentNew_target :
    Core.targetView spec (Integrated.erase reloadingAgentNew) .agent =
      some agentView := by
  apply agent_target_at
  · simp [reloadingAgentNew, activeModelNew, reloadingModelNew, activeApiNew,
      reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]
  · simp [reloadingAgentNew, activeModelNew, reloadingModelNew, activeApiNew,
      reloadingApiNew, inserted, Extended.insertEpoch,
      Extended.insertLifecycle, removed, Extended.removeEpoch,
      Extended.removeLifecycle, normalized, normalizedLifecycle,
      inactiveModel, inactiveAgent, retiringAgent, retiringModel,
      retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
      initial, initialLifecycle]
  · exact modelProvider_eq_some_reloadingAgent

/-- Explicit six-step startup after inserting `apiNew`. -/
theorem insertion_normalization_schedule :
    Relation.ReflTransGen (Integrated.Step spec program)
      inserted.lifecycle final.lifecycle := by
  apply Relation.ReflTransGen.head
  · exact ⟨.apiNew,
      Integrated.StepAt.begin rfl inserted_api_target⟩
  · apply Relation.ReflTransGen.head
    · exact ⟨.apiNew,
        Integrated.StepAt.finish rfl reloadingApiNew_target⟩
    · apply Relation.ReflTransGen.head
      · exact ⟨.model,
          Integrated.StepAt.begin rfl activeApiNew_model_target⟩
      · apply Relation.ReflTransGen.head
        · exact ⟨.model,
            Integrated.StepAt.finish rfl reloadingModelNew_target⟩
        · apply Relation.ReflTransGen.head
          · exact ⟨.agent,
              Integrated.StepAt.begin rfl activeModelNew_agent_target⟩
          · apply Relation.ReflTransGen.single
            exact ⟨.agent,
              Integrated.StepAt.finish rfl reloadingAgentNew_target⟩

theorem final_api_target :
    Core.targetView spec (Integrated.erase final.lifecycle) .apiNew =
      some emptyView := by
  apply apiNew_target
  · simp [final, finalLifecycle, reloadingAgentNew, activeModelNew,
      reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · simp [final, finalLifecycle, reloadingAgentNew, activeModelNew,
      reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]

private theorem apiProvider_eq_some_final :
    Core.provider spec (Integrated.erase final.lifecycle) .api = some .apiNew := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [final, finalLifecycle, reloadingAgentNew,
      activeModelNew, reloadingModelNew, activeApiNew, reloadingApiNew,
      inserted, Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨emptyView, by simp [final, finalLifecycle, reloadingAgentNew,
      activeModelNew, reloadingModelNew, activeApiNew, Integrated.erasePhase,
      Integrated.State.setPhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, final, finalLifecycle,
        reloadingAgentNew, activeModelNew, reloadingModelNew, activeApiNew,
        reloadingApiNew, inserted, Extended.insertEpoch,
        Extended.insertLifecycle, removed, Extended.removeEpoch,
        Extended.removeLifecycle, normalized, normalizedLifecycle,
        inactiveModel, inactiveAgent, retiringAgent, retiringModel,
        retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
        initial, initialLifecycle, spec, Core.active, Integrated.erasePhase,
        Integrated.State.setPhase, Integrated.State.setWorld,
        Effects.recover, Effects.identityAccumulator] at hcandidate ⊢

theorem final_model_target :
    Core.targetView spec (Integrated.erase final.lifecycle) .model =
      some modelNewView := by
  apply modelNew_target_at
  · simp [final, finalLifecycle, reloadingAgentNew, activeModelNew,
      reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · simp [final, finalLifecycle, reloadingAgentNew, activeModelNew,
      reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · exact apiProvider_eq_some_final

private theorem modelProvider_eq_some_final :
    Core.provider spec (Integrated.erase final.lifecycle) .model = some .model := by
  apply Core.provider_eq_some_iff.mpr
  constructor
  · refine ⟨by simp [final, finalLifecycle, reloadingAgentNew,
      activeModelNew, reloadingModelNew, activeApiNew, reloadingApiNew,
      inserted, Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle], ?_, by simp [spec]⟩
    exact ⟨modelNewView, by simp [final, finalLifecycle, reloadingAgentNew,
      activeModelNew, Integrated.erasePhase, Integrated.State.setPhase]⟩
  · intro candidate hcandidate
    cases candidate <;>
      simp [Core.TargetProviderValid, final, finalLifecycle,
        reloadingAgentNew, activeModelNew, reloadingModelNew, activeApiNew,
        reloadingApiNew, inserted, Extended.insertEpoch,
        Extended.insertLifecycle, removed, Extended.removeEpoch,
        Extended.removeLifecycle, normalized, normalizedLifecycle,
        inactiveModel, inactiveAgent, retiringAgent, retiringModel,
        retiringApi, retired, Extended.retireEpoch, Extended.retireLifecycle,
        initial, initialLifecycle, spec, Core.active, Integrated.erasePhase,
        Integrated.State.setPhase, Integrated.State.setWorld,
        Effects.recover, Effects.identityAccumulator] at hcandidate ⊢

theorem final_agent_target :
    Core.targetView spec (Integrated.erase final.lifecycle) .agent =
      some agentView := by
  apply agent_target_at
  · simp [final, finalLifecycle, reloadingAgentNew, activeModelNew,
      reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · simp [final, finalLifecycle, reloadingAgentNew, activeModelNew,
      reloadingModelNew, activeApiNew, reloadingApiNew, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle]
  · exact modelProvider_eq_some_final

theorem final_quiet : Core.quiet spec (Integrated.erase final.lifecycle) := by
  intro fiber
  cases fiber
  · simpa [Core.LocallyQuiet, final, finalLifecycle, reloadingAgentNew,
      Integrated.erasePhase] using final_agent_target
  · simpa [Core.LocallyQuiet, final, finalLifecycle, reloadingAgentNew,
      activeModelNew, Integrated.erasePhase, Integrated.State.setPhase] using
      final_model_target
  · simp [Core.LocallyQuiet, final, finalLifecycle, reloadingAgentNew,
      activeModelNew, reloadingModelNew, activeApiNew, reloadingApiNew,
      inserted, Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle,
      Integrated.erasePhase, Core.targetView_eq_none_iff_not_ready,
      Core.TargetReady]
  · simpa [Core.LocallyQuiet, final, finalLifecycle, reloadingAgentNew,
      activeModelNew, reloadingModelNew, activeApiNew, Integrated.erasePhase,
      Integrated.State.setPhase] using final_api_target

/-- The concrete model commits to the fresh API identity at the final quiet
endpoint. -/
theorem final_model_commits_apiNew :
    Core.committedView (Integrated.erase final.lifecycle) .model =
        some modelNewView ∧
      modelNewView .api = some .apiNew := by
  constructor
  · simp [final, finalLifecycle, reloadingAgentNew, activeModelNew,
      Integrated.erasePhase, Integrated.State.setPhase, Core.committedView]
  · rfl

/-- The two explicit normalization schedules and the final observation, before
packaging the three quiet-boundary registry actions. -/
theorem checked_schedule_and_observation :
    Relation.ReflTransGen (Integrated.Step spec program)
        retired.lifecycle normalized.lifecycle ∧
      Relation.ReflTransGen (Integrated.Step spec program)
        inserted.lifecycle final.lifecycle ∧
      Core.quiet spec (Integrated.erase final.lifecycle) ∧
      Core.committedView (Integrated.erase final.lifecycle) .model =
        some modelNewView ∧
      modelNewView .api = some .apiNew :=
  ⟨retire_normalization_schedule, insertion_normalization_schedule,
    final_quiet, final_model_commits_apiNew⟩

theorem initial_wellFormed :
    Integrated.CoreWellFormed spec initialLifecycle := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro provider consumer hprovider hconsumer hne
    change provider ∈ initialLifecycle.registered at hprovider
    change consumer ∈ initialLifecycle.registered at hconsumer
    cases provider <;> cases consumer <;>
      simp [initialLifecycle, spec] at hprovider hconsumer hne ⊢
  · intro fiber hregistered
    change fiber ∉ initialLifecycle.registered at hregistered
    change Integrated.erasePhase (initialLifecycle.phase fiber) = .inactive
    cases fiber <;>
      simp [initialLifecycle, Integrated.erasePhase] at hregistered ⊢
  · intro fiber view hview key
    cases fiber <;>
      simp [initialLifecycle, Core.committedView, Integrated.erasePhase] at hview
    · subst view
      cases key <;> simp [agentView, spec]
    · subst view
      cases key <;> simp [modelOldView, spec]
    · subst view
      cases key <;> simp [emptyView, spec]
  · intro fiber view hview key provider hbinding
    cases fiber <;>
      simp [initialLifecycle, Core.committedView, Integrated.erasePhase] at hview
    · subst view
      cases key <;> cases provider <;>
        simp [agentView, Core.CommittedProviderValid, Core.installed,
          initialLifecycle, spec, Integrated.erasePhase] at hbinding ⊢
    · subst view
      cases key <;> cases provider <;>
        simp [modelOldView, Core.CommittedProviderValid, Core.installed,
          initialLifecycle, spec, Integrated.erasePhase] at hbinding ⊢
    · subst view
      cases key <;> cases provider <;>
        simp [emptyView] at hbinding

/-- Concrete orientation audit for `committed_implies_priority`: the retained
Model binding induces `API_old → Model`, never the reversed edge. -/
theorem initial_committed_priority_orientation :
    Core.Priority spec (Integrated.erase initialLifecycle) .apiOld .model ∧
      ¬ Core.Priority spec (Integrated.erase initialLifecycle) .model .apiOld := by
  constructor
  · apply Core.committed_implies_priority
      (c := .model) (p := .apiOld) (v := modelOldView) (k := .api)
      initial_wellFormed
    · simp [initialLifecycle, Integrated.erasePhase, Core.committedView]
    · rfl
  · simp [Core.Priority, Core.PriorityOn, initialLifecycle, spec]

def priorityRank : Fiber → Nat
  | .agent => 0
  | .model => 1
  | .apiOld | .apiNew => 2

private theorem acyclic_of_registered
    (registered : Finset Fiber)
    (hedge : ∀ {child parent},
      Core.PrioritySuccOn spec registered child parent →
        priorityRank child < priorityRank parent) :
    WellFounded (Core.PrioritySuccOn spec registered) :=
  (InvImage.wf priorityRank Nat.lt_wfRel.wf).mono fun _ _ edge =>
    hedge edge

theorem initial_acyclic :
    Core.PriorityAcyclic spec (Integrated.erase initialLifecycle) := by
  apply acyclic_of_registered
  intro child parent edge
  cases child <;> cases parent <;>
    simp [Core.PrioritySuccOn, Core.PriorityOn, initialLifecycle, spec,
      priorityRank] at edge ⊢

theorem initial_sound : initial.Sound spec := by
  exact ⟨initial_wellFormed, initial_acyclic, by simp [initial, initialLifecycle]⟩

theorem retire_action : Extended.Action spec initial retired :=
  .retire initial_sound (by simpa [initial] using initial_quiet)
    (by simp [initial, initialLifecycle])
    (by simp [initial, initialLifecycle])

private theorem integratedStep_registered_eq
    {source target : Integrated.State Fiber Key Unit}
    (step : Integrated.Step spec program source target) :
    target.registered = source.registered := by
  rcases step with ⟨actor, actorStep⟩
  exact actorStep.registered_eq

private theorem integratedStep_retired_eq
    {source target : Integrated.State Fiber Key Unit}
    (step : Integrated.Step spec program source target) :
    target.retired = source.retired := by
  rcases step with ⟨actor, actorStep⟩
  exact actorStep.retired_eq

private theorem integratedReach_registered_eq
    {source target : Integrated.State Fiber Key Unit}
    (reach : Relation.ReflTransGen (Integrated.Step spec program) source target) :
    target.registered = source.registered := by
  induction reach with
  | refl => rfl
  | tail reach step ih => exact (integratedStep_registered_eq step).trans ih

private theorem integratedReach_retired_eq
    {source target : Integrated.State Fiber Key Unit}
    (reach : Relation.ReflTransGen (Integrated.Step spec program) source target) :
    target.retired = source.retired := by
  induction reach with
  | refl => rfl
  | tail reach step ih => exact (integratedStep_retired_eq step).trans ih

private theorem integratedReach_preserves_wellFormed
    {source target : Integrated.State Fiber Key Unit}
    (wf : Integrated.CoreWellFormed spec source)
    (reach : Relation.ReflTransGen (Integrated.Step spec program) source target) :
    Integrated.CoreWellFormed spec target := by
  induction reach with
  | refl => exact wf
  | tail reach step ih =>
      exact Integrated.Step.preserve_coreWellFormed spec program ih step

private theorem normalization_target_sound
    {source target : Extended.OrchState Fiber Key Unit}
    (sound : source.Sound spec)
    (reach : Relation.ReflTransGen (Integrated.Step spec program)
      source.lifecycle target.lifecycle)
    (everRegisteredEq : target.everRegistered = source.everRegistered) :
    target.Sound spec := by
  have hregistered := integratedReach_registered_eq reach
  refine ⟨integratedReach_preserves_wellFormed sound.1 reach, ?_, ?_⟩
  · simpa [Core.PriorityAcyclic, Integrated.erase, hregistered] using sound.2.1
  · intro fiber hfiber
    rw [everRegisteredEq]
    apply sound.2.2
    rw [← hregistered]
    exact hfiber

theorem normalized_sound : normalized.Sound spec := by
  apply normalization_target_sound retire_action.preserves_sound
    retire_normalization_schedule
  rfl

theorem retire_normalization :
    Extended.Normalization spec program retired normalized where
  schedule := retire_normalization_schedule
  quiet := normalized_quiet
  targetSound := normalized_sound
  registered_eq := integratedReach_registered_eq retire_normalization_schedule
  retired_eq := integratedReach_retired_eq retire_normalization_schedule
  everRegistered_eq := rfl

private theorem normalized_integrated_phase_inactive (fiber : Fiber) :
    normalizedLifecycle.phase fiber = .inactive := by
  cases fiber <;> simp [normalizedLifecycle, inactiveModel, inactiveAgent,
    retiringAgent, retiringModel, retiringApi, retired,
    Extended.retireEpoch, Extended.retireLifecycle, initial,
    initialLifecycle, Integrated.State.setPhase,
    Integrated.State.setWorld, Effects.recover,
    Effects.identityAccumulator]

private theorem normalized_phase_inactive (fiber : Fiber) :
    (Integrated.erase normalizedLifecycle).phase fiber = .inactive := by
  change Integrated.erasePhase (normalizedLifecycle.phase fiber) = .inactive
  rw [normalized_integrated_phase_inactive]
  rfl

private theorem removed_integrated_phase_inactive (fiber : Fiber) :
    removed.lifecycle.phase fiber = .inactive := by
  simpa [removed, Extended.removeEpoch, Extended.removeLifecycle, normalized] using
    normalized_integrated_phase_inactive fiber

private theorem removed_phase_inactive (fiber : Fiber) :
    (Integrated.erase removed.lifecycle).phase fiber = .inactive := by
  change Integrated.erasePhase (removed.lifecycle.phase fiber) = .inactive
  rw [removed_integrated_phase_inactive]
  rfl

private theorem inserted_phase_inactive (fiber : Fiber) :
    (Integrated.erase inserted.lifecycle).phase fiber = .inactive := by
  simpa [inserted, Extended.insertEpoch, Extended.insertLifecycle,
    Integrated.erase] using removed_phase_inactive fiber

private theorem wellFormed_of_all_inactive
    (state : Core.State Fiber Key)
    (singleSource : Core.SingleSource spec state)
    (inactive : ∀ fiber, state.phase fiber = .inactive) :
    Core.WellFormed spec state := by
  refine ⟨singleSource, fun fiber _ => inactive fiber, ?_, ?_⟩
  · intro fiber view hview
    rw [Core.committedView, inactive fiber] at hview
    simp at hview
  · intro fiber view hview
    rw [Core.committedView, inactive fiber] at hview
    simp at hview

private theorem unloadable_of_all_inactive
    (state : Core.State Fiber Key)
    (inactive : ∀ fiber, state.phase fiber = .inactive)
    (provider : Fiber) : Core.unloadable state provider := by
  rintro ⟨consumer, view, key, hview, _⟩
  rw [Core.committedView, inactive consumer] at hview
  simp at hview

theorem removed_wellFormed :
    Integrated.CoreWellFormed spec removed.lifecycle := by
  apply wellFormed_of_all_inactive
  · intro provider consumer hprovider hconsumer hne
    cases provider <;> cases consumer <;>
      simp [removed, Extended.removeEpoch, Extended.removeLifecycle,
        normalized, normalizedLifecycle, inactiveModel, inactiveAgent,
        retiringAgent, retiringModel, retiringApi, retired,
        Extended.retireEpoch, Extended.retireLifecycle, initial,
        initialLifecycle, Integrated.erase, spec] at hprovider hconsumer hne ⊢
  · exact removed_phase_inactive

theorem removed_acyclic :
    Core.PriorityAcyclic spec (Integrated.erase removed.lifecycle) := by
  apply acyclic_of_registered
  intro child parent edge
  cases child <;> cases parent <;>
    simp [Core.PrioritySuccOn, Core.PriorityOn, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle, spec,
      priorityRank] at edge ⊢

theorem remove_action : Extended.Action spec normalized removed :=
  .remove normalized_sound normalized_quiet
    (by simp [normalized, normalizedLifecycle, inactiveModel, inactiveAgent,
      retiringAgent, retiringModel, retiringApi, retired,
      Extended.retireEpoch, Extended.retireLifecycle, initial,
      initialLifecycle])
    (by simp [normalized, normalizedLifecycle, inactiveModel, inactiveAgent,
      retiringAgent, retiringModel, retiringApi, retired,
      Extended.retireEpoch, Extended.retireLifecycle, initial,
      initialLifecycle])
    (normalized_integrated_phase_inactive .apiOld)
    (unloadable_of_all_inactive _ normalized_phase_inactive .apiOld)
    removed_wellFormed removed_acyclic

theorem removed_sound : removed.Sound spec := remove_action.preserves_sound

theorem inserted_wellFormed :
    Integrated.CoreWellFormed spec inserted.lifecycle := by
  apply wellFormed_of_all_inactive
  · intro provider consumer hprovider hconsumer hne
    cases provider <;> cases consumer <;>
      simp [inserted, Extended.insertEpoch, Extended.insertLifecycle,
        removed, Extended.removeEpoch, Extended.removeLifecycle, normalized,
        normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
        retiringModel, retiringApi, retired, Extended.retireEpoch,
        Extended.retireLifecycle, initial, initialLifecycle,
        Integrated.erase, spec] at hprovider hconsumer hne ⊢
  · exact inserted_phase_inactive

theorem inserted_acyclic :
    Core.PriorityAcyclic spec (Integrated.erase inserted.lifecycle) := by
  apply acyclic_of_registered
  intro child parent edge
  cases child <;> cases parent <;>
    simp [Core.PrioritySuccOn, Core.PriorityOn, inserted,
      Extended.insertEpoch, Extended.insertLifecycle, removed,
      Extended.removeEpoch, Extended.removeLifecycle, normalized,
      normalizedLifecycle, inactiveModel, inactiveAgent, retiringAgent,
      retiringModel, retiringApi, retired, Extended.retireEpoch,
      Extended.retireLifecycle, initial, initialLifecycle, spec,
      priorityRank] at edge ⊢

theorem insert_action : Extended.Action spec removed inserted :=
  .insert removed_sound removed_quiet
    (by simp [removed, Extended.removeEpoch, normalized, initial])
    (removed_integrated_phase_inactive .apiNew)
    inserted_wellFormed inserted_acyclic

theorem inserted_sound : inserted.Sound spec := insert_action.preserves_sound

theorem final_sound : final.Sound spec := by
  apply normalization_target_sound inserted_sound insertion_normalization_schedule
  rfl

theorem insertion_normalization :
    Extended.Normalization spec program inserted final where
  schedule := insertion_normalization_schedule
  quiet := final_quiet
  targetSound := final_sound
  registered_eq := integratedReach_registered_eq insertion_normalization_schedule
  retired_eq := integratedReach_retired_eq insertion_normalization_schedule
  everRegistered_eq := rfl

/-- Fully concrete quiet-only replacement derivation. -/
def replacement_derivation :
    Extended.ReplacementDerivation spec program initial .apiOld .apiNew where
  retired := retired
  normalized := normalized
  removed := removed
  inserted := inserted
  final := final
  retireAction := retire_action
  retired_eq := rfl
  normalizeRetired := retire_normalization
  removeAction := remove_action
  removed_eq := rfl
  insertAction := insert_action
  inserted_eq := rfl
  normalizeInserted := insertion_normalization

/-- The requested checked end-to-end scenario: explicit five-stage derivation,
explicit normalization schedules, final quietness, and a committed binding to
the fresh API provider. -/
theorem checked_agent_model_api_replacement :
    ∃ derivation :
        Extended.ReplacementDerivation spec program initial .apiOld .apiNew,
      derivation.retired = retired ∧
      derivation.normalized = normalized ∧
      derivation.removed = removed ∧
      derivation.inserted = inserted ∧
      derivation.final = final ∧
      Core.quiet spec (Integrated.erase derivation.final.lifecycle) ∧
      Core.committedView (Integrated.erase derivation.final.lifecycle) .model =
          some modelNewView ∧
      modelNewView .api = some .apiNew :=
  ⟨replacement_derivation, rfl, rfl, rfl, rfl, rfl, final_quiet,
    final_model_commits_apiNew⟩

end Cordis.Examples.AgentModelApiReplacement
