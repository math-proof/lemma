import { defineConfig } from "vite";
import vue from "@vitejs/plugin-vue";
import path from "path";
import { fileURLToPath } from "url";

const root = path.dirname(fileURLToPath(import.meta.url));

export default defineConfig({
	plugins: [vue()],
	build: {
		outDir: path.join(root, "dist/vue"),
		emptyOutDir: true,
		cssCodeSplit: false,
		rollupOptions: {
			input: {
				vuePages: path.join(root, "js/vuePages.js"),
				codemirrorBoot: path.join(root, "js/codemirrorBoot.js"),
			},
			output: {
				format: "es",
				entryFileNames(chunk) {
					if (chunk.name === "vuePages") return "pages.js";
					if (chunk.name === "codemirrorBoot") return "codemirror.js";
					return "chunks/[name]-[hash].js";
				},
				chunkFileNames: "chunks/[name]-[hash].js",
				assetFileNames: "assets/[name][extname]",
			},
		},
	},
});
