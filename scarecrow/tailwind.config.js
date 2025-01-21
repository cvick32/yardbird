/** @type {import('tailwindcss').Config} */
export default {
  content: ["./index.html", "./src/**/*.{js,ts,jsx,tsx}"],
  theme: {
    extend: {
      colors: {
        "solarized-base03": "#002b36",
        "solarized-base02": "#073642",
        "solarized-base01": "#586e75",
        "solarized-base00": "#657b83",
        "solarized-base0": "#839496",
        "solarized-base1": "#93a1a1",
        "solarized-base2": "#eee8d5",
        "solarized-base3": "#fdf6e3",
      },
    },
    screens: {
      md: "1000px",
    },
  },
  plugins: [],
};
