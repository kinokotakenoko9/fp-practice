import { NextRequest, NextResponse } from "next/server";
import lam from "@/lib/main.bc";

export async function POST(req: NextRequest) {
  try {
    const { input, maxReductions, showVarIds, showDeltaReduction, strategy } =
      await req.json();
    let result;
    const mr = maxReductions || 0;

    // @ts-expect-error fine
    if (strategy === "AO")
      result = lam.get_ao(input, mr, showVarIds, showDeltaReduction);
    // @ts-expect-error fine
    else if (strategy === "NO")
      result = lam.get_no(input, mr, showVarIds, showDeltaReduction);
    // @ts-expect-error fine
    else if (strategy === "CBN")
      result = lam.get_cbn(input, mr, showVarIds, showDeltaReduction);
    // @ts-expect-error fine
    else if (strategy === "CBV")
      result = lam.get_cbv(input, mr, showVarIds, showDeltaReduction);

    return NextResponse.json({ result });
  } catch (error) {
    console.error("Backend processing error:", error);
    return NextResponse.json(
      { error: "Failed to process lambda" },
      { status: 500 }
    );
  }
}
