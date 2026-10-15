import { execFile } from "node:child_process";
import { mkdir, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { promisify } from "node:util";
import { expect } from "vitest";

import { parseEvidence } from "../../../src/domain/evidence.js";
import { createApplicationMcpHarness } from "../../fixtures/applicationMcpHarness.js";
import { verifyJavaScriptReturnShapes } from "../../fixtures/javascriptReturnShapes.js";
import { createTestTempDirectory } from "../../fixtures/temporaryDirectory.js";
import { cliTest } from "../../support/cli/cliFixture.js";

const source = `
export function captured(x) { const saved=x; x=2; return {type:"ok",value:saved}; }
export function assigned(x) { x=2; const saved=x; return {value:saved}; }
export function between(x) { const before=x; x=2; const after=x; return {before,after}; }
export function intermediate(x) { x=1; const saved=x; x=2; return {value:saved}; }
export function nested(x) { let saved; { saved=x; } x=2; return {value:saved}; }
export function alias(x) { const first=x; const saved=first; x=2; return {value:saved}; }
export function defaulted(x=1) { const saved=x; x=2; return {value:saved}; }
export function destructured({x}) { const saved=x; x=2; return {value:saved}; }
export function local() { let value="before"; value="after"; return {value}; }
`;

cliTest(
  "preserves incoming values and proven assignments through CLI and stdio MCP",
  async ({ cli }) => {
    const oracle = await promisify(execFile)(
      process.execPath,
      [
        "--input-type=module",
        "-e",
        `${source}
console.log(JSON.stringify([captured(5),assigned(5),between(5),intermediate(5),nested(5),alias(5),defaulted(5),destructured({x:5}),local()]));`,
      ],
      { timeout: 10_000 },
    );
    expect(JSON.parse(oracle.stdout)).toEqual([
      { type: "ok", value: 5 },
      { value: 2 },
      { before: 5, after: 2 },
      { value: 1 },
      { value: 5 },
      { value: 5 },
      { value: 5 },
      { value: 5 },
      { value: "after" },
    ]);
    await verifyJavaScriptReturnShapes(cli, source, (fields) => {
      for (const name of [
        "captured",
        "nested",
        "alias",
        "defaulted",
        "destructured",
      ])
        expect(fields(name)).toContainEqual(
          expect.objectContaining({ path: "/value", state: "unknown" }),
        );
      expect(fields("captured")).toContainEqual(
        expect.objectContaining({
          path: "/type",
          state: "literal",
          value: "ok",
        }),
      );
      expect(fields("assigned")).toContainEqual(
        expect.objectContaining({ path: "/value", state: "literal", value: 2 }),
      );
      expect(fields("local")).toContainEqual(
        expect.objectContaining({
          path: "/value",
          state: "literal",
          value: "after",
        }),
      );
      expect(fields("intermediate")).toContainEqual(
        expect.objectContaining({ path: "/value", state: "literal", value: 1 }),
      );
      expect(fields("between")).toContainEqual(
        expect.objectContaining({ path: "/before", state: "unknown" }),
      );
      expect(fields("between")).toContainEqual(
        expect.objectContaining({ path: "/after", state: "literal", value: 2 }),
      );
    });
  },
  120_000,
);

cliTest(
  "distinguishes delayed instance values from immediate static fields and computed keys",
  async ({ cli }) => {
    const fieldsSource = `
export function delayed() { let x=0; class C { field=(x=1) } return {value:x}; }
export function incoming(x) { class C { field=(x=1) } return {value:x}; }
export function delayedPrivate() { let x=0; class C { #field=(x=1) } return {value:x}; }
export function staticField() { let x=0; class C { static field=(x=1) } return {value:x}; }
export function staticPrivate() { let x=0; class C { static #field=(x=1) } return {value:x}; }
export function computedKey() { let x=0; class C { [x=1]=7 } return {value:x}; }
`;
    const oracle = await promisify(execFile)(
      process.execPath,
      [
        "--input-type=module",
        "-e",
        `${fieldsSource}
console.log(JSON.stringify([delayed(),incoming(5),delayedPrivate(),staticField(),staticPrivate(),computedKey()]));`,
      ],
      { timeout: 10_000 },
    );
    expect(JSON.parse(oracle.stdout)).toEqual([
      { value: 0 },
      { value: 5 },
      { value: 0 },
      { value: 1 },
      { value: 1 },
      { value: 1 },
    ]);
    await verifyJavaScriptReturnShapes(cli, fieldsSource, (fields) => {
      for (const name of ["delayed", "incoming", "delayedPrivate"])
        expect(fields(name)).toContainEqual(
          expect.objectContaining({ path: "/value", state: "unknown" }),
        );
      for (const name of ["staticField", "staticPrivate", "computedKey"])
        expect(fields(name)).toContainEqual(
          expect.objectContaining({
            path: "/value",
            state: "literal",
            value: 1,
          }),
        );
    });
  },
  120_000,
);

cliTest(
  "keeps a captured parameter unknown when comparing export shapes through CLI and MCP",
  async ({ cli }) => {
    const root = await createTestTempDirectory("rea-captured-comparison-");
    const evidence = [];
    for (const [side, body] of [
      ["left", 'const saved=x; x=2; return {type:"ok",value:saved};'],
      ["right", 'return {type:"ok",value:2};'],
    ] as const) {
      const directory = join(root, side);
      await mkdir(directory);
      await writeFile(
        join(directory, "main.mjs"),
        `export function read(x) { ${body} }`,
      );
      const response = await cli.run({
        arguments: ["analyze-javascript-application", directory, "--json"],
      });
      expect(response.exitCode, response.stderr).toBe(0);
      evidence.push(parseEvidence(response.json));
    }
    const [left, right] = evidence;
    if (left === undefined || right === undefined)
      throw new Error("Missing source Evidence");
    const input = {
      left,
      right,
      left_module_path: "main.mjs",
      left_export_name: "read",
      right_module_path: "main.mjs",
      right_export_name: "read",
    };
    const path = join(root, "comparison.json");
    await writeFile(path, JSON.stringify(input));
    const response = await cli.run({
      arguments: ["compare-javascript-export-shapes", path, "--json"],
    });
    expect(response.exitCode, response.stderr).toBe(0);
    const comparison = parseEvidence(response.json);
    expect(comparison.evidence_links).toEqual([
      left.evidence_id,
      right.evidence_id,
    ]);
    expect(comparison.normalized_result).toMatchObject({
      summary: {
        added: 0,
        removed: 0,
        changed: 0,
        unknown: 1,
      },
      changes: [expect.objectContaining({ path: "/value", status: "unknown" })],
    });
    const harness = await createApplicationMcpHarness();
    try {
      const reply = await harness.client.callTool({
        name: "compare_javascript_export_shapes",
        arguments: input,
      });
      expect(reply.isError).not.toBe(true);
      expect(parseEvidence(reply.structuredContent)).toEqual(comparison);
      const retained = await harness.client.callTool({
        name: "compare_javascript_export_shapes",
        arguments: {
          ...input,
          left: { kind: "retained-evidence", evidence_id: left.evidence_id },
          right: { kind: "retained-evidence", evidence_id: right.evidence_id },
        },
      });
      expect(retained.isError).not.toBe(true);
      expect(parseEvidence(retained.structuredContent)).toEqual(comparison);
    } finally {
      await harness.close();
    }
  },
  120_000,
);
