"use client";

import { useEffect, useState } from "react";
// @ts-expect-error fine
import lam from "../public/js/main.bc.js";
import CodeMirror from "@uiw/react-codemirror";
import { StreamLanguage } from "@codemirror/language";
import { basicSetup } from "codemirror";
import { haskell } from "@codemirror/legacy-modes/mode/haskell";
import { Checkbox } from "@/components/ui/checkbox";
import { Input } from "@/components/ui/input";
import { Label } from "@/components/ui/label";
import { RadioGroup, RadioGroupItem } from "@/components/ui/radio-group";
import macros from "./config";

export default function Home() {
  const [input, setInput] = useState<string>(macros);
  const [lambda, setLambda] = useState<string>("");
  const [showVarIds, setShowVarIds] = useState(false);
  const [maxReductions, setMaxReductions] = useState(10);
  const [strategy, setStrategy] = useState("AO");

  useEffect(() => {
    let res;
    const mr = maxReductions || 0;
    if (strategy === "AO") res = lam.get_ao(input, mr, showVarIds);
    else if (strategy === "NO") res = lam.get_no(input, mr, showVarIds);
    else if (strategy === "CBN") res = lam.get_cbn(input, mr, showVarIds);
    else if (strategy === "CBV") res = lam.get_cbv(input, mr, showVarIds);
    setLambda(res);
  }, [input, maxReductions, showVarIds, strategy]);

  return (
    <div className="items-center justify-items-center min-h-screen p-2 pb-16 gap-16 sm:p-2 font-[family-name:var(--font-geist-sans)]">
      <div className="flex flex-col sm:flex-row gap-4 p-4">
        <div className="flex-1 min-w-0">
          <CodeMirror
            value={input}
            height="400px"
            onChange={(val) => {
              setInput(val);
            }}
            extensions={[basicSetup, StreamLanguage.define(haskell)]}
          />
        </div>

        <div className="flex flex-col gap-6 p-4 border rounded-sm min-w-max">
          {/* Show Variable IDs */}
          <div className="flex items-center space-x-2">
            <Checkbox
              checked={showVarIds}
              onCheckedChange={(val) => setShowVarIds(val as boolean)}
            />
            <Label>Show variable IDs</Label>
          </div>

          {/* Max Reductions */}
          <div className="grid w-full max-w-sm items-center gap-1.5">
            <Label htmlFor="reductions">Max reductions</Label>
            <Input
              id="reductions"
              type="number"
              value={maxReductions.toString()}
              onChange={(e) => {
                const val = parseInt(e.target.value, 10);
                if ((val || 0) <= 10000) setMaxReductions(val);
                else setMaxReductions(maxReductions);
              }}
              className="border rounded px-2 py-1 w-full"
            />
          </div>

          {/* Strategy Selection */}
          <div className="w-2/3 space-y-3">
            <Label>Evaluation strategy</Label>
            <RadioGroup
              defaultValue="AO"
              onValueChange={(val) => {
                setStrategy(val);
              }}
            >
              <div className="flex items-center space-x-2">
                <RadioGroupItem value="AO" id="r1" />
                <Label htmlFor="r1">Applicative Order</Label>
              </div>
              <div className="flex items-center space-x-2">
                <RadioGroupItem value="NO" id="r2" />
                <Label htmlFor="r2">Normal Order</Label>
              </div>
              <div className="flex items-center space-x-2">
                <RadioGroupItem value="CBV" id="r3" />
                <Label htmlFor="r3">Call-by-Value</Label>
              </div>
              <div className="flex items-center space-x-2">
                <RadioGroupItem value="CBN" id="r4" />
                <Label htmlFor="r4">Call-by-Name</Label>
              </div>
            </RadioGroup>
          </div>
        </div>
      </div>

      <div
        dangerouslySetInnerHTML={{ __html: lambda }}
        className="lambda-output m-4 p-4 border rounded-sm bg-gray-50 text-sm font-mono text-gray-800"
      ></div>
    </div>
  );
}
