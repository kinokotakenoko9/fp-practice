"use client"

import { useState } from 'react';
// @ts-expect-error fine
import lam from "../public/js/main.bc.js";
import { Button } from '../components/ui/button';
import { Textarea } from '../components/ui/textarea';

export default function Home() {
  const [input, setInput] = useState<string>("");
  const [result, setResult] = useState<string>("");

  const handleSubmit = () => {
    const output = lam.get_ao(input, 1000); // Assuming this function returns a string
    setResult(output);
  };


  return (
    <div className="grid grid-rows-[20px_1fr_20px] items-center justify-items-center min-h-screen p-8 pb-20 gap-16 sm:p-20 font-[family-name:var(--font-geist-sans)]">
      <div>
        <Textarea 
          value={input} 
          onChange={(e) => setInput(e.target.value)} 
          placeholder="Enter lambda expression here"
          rows={4}
          className="mb-4"
        />
        <Button onClick={handleSubmit}>Submit</Button>
      </div>
      
      <div 
        dangerouslySetInnerHTML={{ __html: result }} 
        className="mt-8"
      ></div>
    </div>
  );
}
