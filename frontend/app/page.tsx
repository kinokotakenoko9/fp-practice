"use client";

import { useEffect, useRef, useState } from "react";
import CodeMirror from "@uiw/react-codemirror";
import { StreamLanguage } from "@codemirror/language";
import { basicSetup } from "codemirror";
import { haskell } from "@codemirror/legacy-modes/mode/haskell";
import { Checkbox } from "@/components/ui/checkbox";
import { Input } from "@/components/ui/input";
import { Label } from "@/components/ui/label";
import { RadioGroup, RadioGroupItem } from "@/components/ui/radio-group";
import macros from "./config";
import { Button } from "@/components/ui/button";

const LOCAL_STORAGE_KEY = "lambdaEditorMacros";

export default function Home() {
  const [input, setInput] = useState<string>(macros);
  const [lambda, setLambda] = useState<string>("");
  const [showVarIds, setShowVarIds] = useState(false);
  const [showDeltaReduction, setShowDeltaReduction] = useState(true);
  const [maxReductions, setMaxReductions] = useState(10);
  const [strategy, setStrategy] = useState("AO");

  useEffect(() => {
    const storedMacros = localStorage.getItem(LOCAL_STORAGE_KEY);
    if (storedMacros !== null) {
      setInput(storedMacros);
    }
  }, []);

  useEffect(() => {
    localStorage.setItem(LOCAL_STORAGE_KEY, input);
  }, [input]);

  useEffect(() => {
    const fetchData = async () => {
      try {
        const response = await fetch("/api", {
          method: "POST",
          headers: {
            "Content-Type": "application/json",
          },
          body: JSON.stringify({
            input,
            maxReductions,
            showVarIds,
            showDeltaReduction,
            strategy,
          }),
        });

        if (response.ok) {
          const data = await response.json();
          setLambda(data.result);
        } else {
          console.error("Error processing lambda:", response.status);
          setLambda("Error during processing.");
        }
      } catch (error) {
        console.error("Fetch error:", error);
        setLambda("Error during processing.");
      }
    };

    fetchData();
  }, [input, maxReductions, showVarIds, showDeltaReduction, strategy]);

  return (
    <div className="min-h-screen flex flex-col p-4 sm:p-4 font-[family-name:var(--font-geist-sans)]">
      <div className="flex flex-col sm:flex-row gap-4">
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
          {/* Settings Content */}
          <div className="flex flex-col space-y-2">
            <div className="flex items-center space-x-2">
              <Checkbox
                checked={showVarIds}
                onCheckedChange={(val) => setShowVarIds(val as boolean)}
              />
              <Label>Show variable IDs</Label>
            </div>
            <div className="flex items-center space-x-2">
              <Checkbox
                checked={showDeltaReduction}
                onCheckedChange={(val) => setShowDeltaReduction(val as boolean)}
              />
              <Label>Show delta reduction steps</Label>
            </div>
          </div>
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
          <div className="w-full sm:w-auto space-y-3">
            <Label>Evaluation strategy</Label>
            <RadioGroup
              defaultValue="AO"
              onValueChange={(val) => {
                setStrategy(val);
              }}
            >
              <div className="flex items-center space-x-2 whitespace-nowrap">
                <RadioGroupItem value="AO" id="r1" />
                <Label htmlFor="r1">Applicative Order</Label>
              </div>
              <div className="flex items-center space-x-2 whitespace-nowrap">
                <RadioGroupItem value="NO" id="r2" />
                <Label htmlFor="r2">Normal Order</Label>
              </div>
              <div className="flex items-center space-x-2 whitespace-nowrap">
                <RadioGroupItem value="CBV" id="r3" />
                <Label htmlFor="r3">Call-by-Value</Label>
              </div>
              <div className="flex items-center space-x-2 whitespace-nowrap">
                <RadioGroupItem value="CBN" id="r4" />
                <Label htmlFor="r4">Call-by-Name</Label>
              </div>
            </RadioGroup>
          </div>

          <Button
            onClick={() => {
              setInput(macros);
              localStorage.setItem(LOCAL_STORAGE_KEY, macros);
            }}
            style={{ width: "fit-content" }}
          >
            Reset Macros
          </Button>
        </div>
      </div>

      <div
        className="lambda-output mt-8 p-4 border rounded-sm bg-gray-50 text-sm font-mono text-gray-800 overflow-auto w-full"
        dangerouslySetInnerHTML={{ __html: lambda }}
      ></div>
    </div>
  );
}
