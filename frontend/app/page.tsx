"use client";

import { useCallback, useEffect, useState } from "react";
import CodeMirror, { oneDark } from "@uiw/react-codemirror";
import { StreamLanguage } from "@codemirror/language";
import { basicSetup } from "codemirror";
import { haskell } from "@codemirror/legacy-modes/mode/haskell";
import { Checkbox } from "@/components/ui/checkbox";
import { Input } from "@/components/ui/input";
import { Label } from "@/components/ui/label";
import { RadioGroup, RadioGroupItem } from "@/components/ui/radio-group";
import macros from "./config";
import { Button } from "@/components/ui/button";
import { useTheme } from "next-themes";
import { CheckIcon, Link, Moon, Sun } from "lucide-react";

const LOCAL_STORAGE_KEY = "lambdaEditorMacros";
const getURL = (str: string) =>
  `https://fp-practice.vercel.app?lam=${btoa(str)}`;

export default function Home() {
  const [input, setInput] = useState<string>(macros);
  const [lambda, setLambda] = useState<string>("");
  const [showVarIds, setShowVarIds] = useState(false);
  const [showDeltaReduction, setShowDeltaReduction] = useState(true);
  const [showMinimalParens, setShowMinimalParens] = useState(true);
  const [maxReductions, setMaxReductions] = useState(10);
  const [strategy, setStrategy] = useState("AO");
  const { theme, setTheme } = useTheme();
  const [isClient, setIsClient] = useState(false);
  const [hasCopied, setHasCopied] = useState(false);

  useEffect(() => {
    setIsClient(true);
  }, []);

  useEffect(() => {
    const search = window.location.search;
    const urlParams = new URLSearchParams(search);
    const lamValue = urlParams.get("lam");
    if (lamValue) {
      setInput(atob(lamValue));
      return;
    }

    const storedMacros = localStorage.getItem(LOCAL_STORAGE_KEY);
    if (storedMacros !== null) {
      setInput(storedMacros);
    }
  }, []);

  useEffect(() => {
    if (isClient) {
      localStorage.setItem(LOCAL_STORAGE_KEY, input);
    }
  }, [input, isClient]);

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
            showMinimalParens,
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

    if (isClient) fetchData();
  }, [
    input,
    maxReductions,
    showVarIds,
    showDeltaReduction,
    showMinimalParens,
    strategy,
    isClient,
  ]);

  useEffect(() => {
    setTimeout(() => {
      if (hasCopied) setHasCopied(false);
    }, 2000);
  }, [hasCopied]);

  const copyToClipboard = useCallback((val: string) => {
    navigator.clipboard.writeText(`${getURL(val)}`);
    setHasCopied(true);
  }, []);

  const toggleTheme = () => {
    setTheme(theme === "dark" ? "light" : "dark");
  };

  return (
    <div className="min-h-screen flex flex-col p-4 sm:p-4 font-sans">
      <div className="flex flex-col sm:flex-row gap-4">
        <div className="flex-1 min-w-0">
          {isClient ? (
            <CodeMirror
              value={input}
              height="500px"
              onChange={(val) => {
                setInput(val);
              }}
              extensions={[basicSetup, StreamLanguage.define(haskell)]}
              theme={
                theme === "dark" ||
                (theme === "system" &&
                  window.matchMedia("(prefers-color-scheme: dark)").matches)
                  ? oneDark
                  : undefined
              }
            />
          ) : (
            <div style={{ height: "500px" }}></div>
          )}
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
            <div className="flex items-center space-x-2">
              <Checkbox
                checked={showMinimalParens}
                onCheckedChange={(val) => setShowMinimalParens(val as boolean)}
              />
              <Label>Show minimal parentheses</Label>
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
            }}
            style={{ width: "fit-content" }}
          >
            Reset Macros
          </Button>
          <Button
            variant="secondary"
            style={{ width: "fit-content" }}
            onClick={() => {
              copyToClipboard(input);
            }}
          >
            {hasCopied ? (
              <>
                <CheckIcon /> Copy link
              </>
            ) : (
              <>
                <Link /> Copy link
              </>
            )}
          </Button>
          <Button onClick={toggleTheme} variant="outline" size="icon">
            <Sun className="h-[1.2rem] w-[1.2rem] rotate-0 scale-100 transition-all dark:-rotate-90 dark:scale-0" />
            <Moon className="absolute h-[1.2rem] w-[1.2rem] rotate-90 scale-0 transition-all dark:rotate-0 dark:scale-100" />
          </Button>
        </div>
      </div>

      <div
        className="lambda-output mt-8 p-4 border font-mono rounded-sm overflow-auto w-full"
        dangerouslySetInnerHTML={{ __html: lambda }}
      ></div>
    </div>
  );
}
