import { NextRequest, NextResponse } from "next/server";
import lam from "@/lib/main.bc"; // Adjust the import path

export async function POST(req: NextRequest) {
  // Explicitly type 'req' as NextRequest
  try {
    const { input, maxReductions, showVarIds, strategy } = await req.json();
    let result;
    const mr = maxReductions || 0;

    // @ts-expect-error fine
    if (strategy === "AO") result = lam.get_ao(input, mr, showVarIds);
    // @ts-expect-error fine
    else if (strategy === "NO") result = lam.get_no(input, mr, showVarIds);
    // @ts-expect-error fine
    else if (strategy === "CBN") result = lam.get_cbn(input, mr, showVarIds);
    // @ts-expect-error fine
    else if (strategy === "CBV") result = lam.get_cbv(input, mr, showVarIds);

    return NextResponse.json({ result });
  } catch (error) {
    console.error("Backend processing error:", error);
    return NextResponse.json(
      { error: "Failed to process lambda" },
      { status: 500 }
    );
  }
}
