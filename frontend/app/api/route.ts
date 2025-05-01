import { NextRequest, NextResponse } from "next/server";
import lam from "@/lib/main.bc";

export async function POST(req: NextRequest) {
  try {
    const {
      input,
      maxReductions,
      showVarIds,
      showDeltaReduction,
      showMinimalParens,
      strategy,
    } = await req.json();
    let result;
    const mr = maxReductions || 0;

    if (strategy === "AO")
      // @ts-expect-error fine
      result = lam.get_ao(
        input,
        mr,
        showVarIds,
        showDeltaReduction,
        showMinimalParens
      );
    else if (strategy === "NO")
      // @ts-expect-error fine
      result = lam.get_no(
        input,
        mr,
        showVarIds,
        showDeltaReduction,
        showMinimalParens
      );
    else if (strategy === "CBN")
      // @ts-expect-error fine
      result = lam.get_cbn(
        input,
        mr,
        showVarIds,
        showDeltaReduction,
        showMinimalParens
      );
    else if (strategy === "CBV")
      // @ts-expect-error fine
      result = lam.get_cbv(
        input,
        mr,
        showVarIds,
        showDeltaReduction,
        showMinimalParens
      );

    return NextResponse.json({ result });
  } catch (error) {
    console.error("Backend processing error:", error);
    return NextResponse.json(
      { error: "Failed to process lambda" },
      { status: 500 }
    );
  }
}
