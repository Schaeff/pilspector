
const fs = require("fs");
// const path = require("path");
const tty = require('tty');
// const version = require("../package").version;

const { newConstantPolsArray, compile, newCommitPolsArray } = require("pilcom");

const smArith = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_arith/sm_arith.js");
const smBinary = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_binary.js");
const smByte4 = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_byte4.js");
const smGlobal = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_global.js");
const smKeccakF = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_keccakf/sm_keccakf.js");
const smMain = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_main/sm_main.js");
const smMemAlign = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_mem_align.js");
const smMem = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_mem.js");
const smNine2One = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_nine2one.js");
const smNormGate9 = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_norm_gate9.js");
const smPaddingKK = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_padding_kk.js");
const smPaddingKKBit = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_padding_kkbit/sm_padding_kkbit.js");
const smPaddingPG = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_padding_pg.js");
const smPoseidonG = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_poseidong.js");
const smRom = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_rom.js");
// const smStorage = require("@0xpolygonhermez/zkevm-proverjs/src/sm/sm_storage/sm_storage.js");

const { F1Field } = require("ffjavascript");

async function run() {

    // if (typeof(argv.rom) !== "string") {
    //     throw new Error("A rom file needs to be specified")
    // }
    // const romFile = argv.rom.trim();

    // if (typeof(argv.output) !== "string") {
    //     throw new Error("A output file needs to be specified")
    // }
    // const outputFile = argv.output.trim();

    let pilFile = __dirname + "/node_modules/@0xpolygonhermez/zkevm-proverjs/pil/main.pil";
    // if (argv.pil) {
    //     if (typeof(argv.pil) !== "string") {
    //         throw new Error("Pil file needs to be specified with pil option")
    //     }
    //     pilFile = argv.pil.trim();
    // }
    console.log('compile PIL '+pilFile);

    const pilConfig = { defines: {N: 2 ** 21} };

    // if (argv.verbose) {
    //     pilConfig.verbose = true;
    //     if (typeof pilConfig.color === 'undefined') {
    //         pilConfig.color = tty.isatty(process.stdout.fd);
    //     }
    // }

    Fr = new F1Field("0xFFFFFFFF00000001");

    // const rom = JSON.parse(await fs.promises.readFile(romFile, "utf8"));

    const pil = await compile(Fr, pilFile, null, pilConfig);

    const constPols = newConstantPolsArray(pil);

    // BREAK HERE TO DETECT N

    const N = constPols.Main.STEP.length;
    console.log(`N = ${N}`);

    if (constPols.Arith) {
        console.log("Arith...");
        await smArith.buildConstants(constPols.Arith);
    }
    if (constPols.Binary) {
        console.log("Binary...");
        await smBinary.buildConstants(constPols.Binary);
    }
    if (constPols.Byte4) {
        console.log("Byte4...");
        await smByte4.buildConstants(constPols.Byte4);
    }
    if (constPols.Global) {
        console.log("Global...");
        await smGlobal.buildConstants(constPols.Global);
    }
    if (constPols.KeccakF) {
        console.log("KeccakF...");
        await smKeccakF.buildConstants(constPols.KeccakF);
    }
    if (constPols.Main) {
        console.log("Main...");
        await smMain.buildConstants(constPols.Main);
    }
    if (constPols.MemAlign) {
        console.log("MemAlign...");
        await smMemAlign.buildConstants(constPols.MemAlign);
    }
    if (constPols.Mem) {
        console.log("Mem...");
        await smMem.buildConstants(constPols.Mem);
    }
    if (constPols.Nine2One) {
        console.log("Nine2One...");
        await smNine2One.buildConstants(constPols.Nine2One);
    }
    if (constPols.NormGate9) {
        console.log("NormGate9...");
        await smNormGate9.buildConstants(constPols.NormGate9);
    }
    if (constPols.PaddingKK) {
        console.log("PaddingKK...");
        await smPaddingKK.buildConstants(constPols.PaddingKK);
    }
    if (constPols.PaddingKKBit) {
        console.log("PaddingKKBit...");
        await smPaddingKKBit.buildConstants(constPols.PaddingKKBit);
    }
    if (constPols.PaddingPG) {
        console.log("PaddingPG...");
        await smPaddingPG.buildConstants(constPols.PaddingPG);
    }
    if (constPols.PoseidonG) {
        console.log("PoseidonG...");
        await smPoseidonG.buildConstants(constPols.PoseidonG);
    }

    // We are not looking at the Rom at this point

    // if (constPols.Rom) {
    //     console.log("Rom...");
    //     await smRom.buildConstants(constPols.Rom, rom);
    // }

    // storage is ignored because it relies on testvectors. It could be moved back once it's in scope

    // if (constPols.Storage) {
    //     console.log("Storage...");
    //     await smStorage.buildConstants(constPols.Storage);
    // }

    let baseDir = "../constants";

    var used = {}

    for (column in constPols.$$array) {
        let def = constPols.$$defArray[column];

        var fileName = def.name;

        used[fileName] = (used[fileName] === undefined) ? 0 : (used[fileName] + 1);

        var fileName = fileName + "_" + used[fileName];

        // ignore the Rom state machine
        if (!(fileName.startsWith("Rom") || fileName.startsWith("Storage"))) {

            console.log("write ", fileName);

            fileName = fileName.replace(".", "_");
    
            const fd =await fs.promises.open(baseDir + "/" + fileName + ".json", "w+");

            // put all values into [0, p[
            // disabled because we reason over integers for now
            // for(let i = 0; i < constPols.$$n; i++) {
            //     constPols.$$array[column][i] = (constPols.$$array[column][i] < 0n) ? (constPols.$$array[column][i] + 0xffffffff00000001n) : constPols.$$array[column][i];
            // }
        
            await fd.write(JSON.stringify(constPols.$$array[column], (key, value) =>
            typeof value === 'bigint'
                ? value.toString()
                : value));
        
            await fd.close();
        }
    }
    
    console.log("Constants generated succefully!");
}

run().then(()=> {
    process.exit(0);
}, (err) => {
    console.log(err.message);
    console.log(err.stack);
    process.exit(1);
});
