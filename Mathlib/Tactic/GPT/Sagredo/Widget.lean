import ProofWidgets.Component.Basic
import Mathlib.Tactic.GPT.Sagredo.Dialog

namespace Mathlib.Tactic.GPT.Sagredo.Widget

open Lean Elab Meta Tactic



structure Data where
  ci : Elab.ContextInfo
  lctx : LocalContext
  σ : State
  deriving TypeName

end Mathlib.Tactic.GPT.Sagredo.Widget

open Mathlib.Tactic.GPT.Sagredo Widget

open ProofWidgets
open Lean Meta Server Elab Tactic

structure RPCData where
  k : WithRpcRef Data

-- Make it possible for widgets to receive `RPCData`.
#mkrpcenc RPCData

/-- Returns the text of the next query we will make. (But doesn't run it.) -/
@[server_rpc_method]
def nextQuery : RPCData → RequestM (RequestTask (String × RPCData))
  | {k := ⟨{ci, lctx, σ}⟩} => RequestM.asTask do
    let (s, σ') ← Mathlib.Tactic.GPT.Sagredo.nextQuery σ
    pure ⟨s, ⟨ci, lctx, σ'⟩⟩

/-- Runs the next query, and returns the entire response, as well as the extracted code block. -/
@[server_rpc_method]
def runQuery : RPCData → RequestM (RequestTask (String × String × RPCData))
  | {k := ⟨{ci, lctx, σ}⟩} => RequestM.asTask do
    let ((response, sol), σ') ← (do
      askForAssistance (← feedback)
      pure (← latestResponse, ← latestSolution)) σ
    pure ⟨response, sol, ⟨ci, lctx, σ'⟩⟩

@[widget_module]
def runnerWidget : Component RPCData where
  javascript := "
    import { RpcContext, mapRpcError } from '@leanprover/infoview'
    import * as React from 'react';
    const e = React.createElement;

    export default function(data) {
      const [contents, setContents] = React.useState('Sagredo log:')
      const rs = React.useContext(RpcContext)
      const renderQuery = (query) =>
        setContents(currS => currS + '\\n---\\n' + query)
      const renderResponse = (response) =>
        setContents(currS => currS + '\\n---\\n' + response)
      const callSagredo = (data) =>
        rs.call('nextQuery', data)
          .then(resp => {
            const [query, data] = resp
            renderQuery(query)
            rs.call('runQuery', data)
              .then(resp => {
                const [text, [sol, data]] = resp
                renderResponse(text)
                callSagredo(data)
              }) })
          .catch(e => setContents(mapRpcError(e).message))
      return e('div', null, [
        e('button', { onClick: () => callSagredo(data) }, 'Go.'),
        e('pre', null, contents)
      ])
    }
  "

syntax (name := makeRunnerTac) "sagredo!" : tactic

@[tactic makeRunnerTac] def makeRunner : Tactic
  | `(tactic| sagredo!%$tk) => do
    let σ ← createState tk (fun decl => decl.replace "sagredo!" "sorry")
    let (_, σ') ← (do sendSystemMessage systemPrompt) σ
    -- Store the continuation and monad context.
    let data : RPCData := {
      k := ⟨{
        ci := (← ContextInfo.save)
        lctx := (← getLCtx)
        σ := σ'
      }⟩}
    -- Save a widget together with a pointer to `props`.
    savePanelWidgetInfo tk ``runnerWidget (rpcEncode data)
  | _ => throwUnsupportedSyntax

/--please use the refl tactic -/
example : 2 + 2 = 4 := by sagredo!
