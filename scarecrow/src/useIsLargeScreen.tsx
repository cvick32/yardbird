import { useMediaQuery } from "usehooks-ts";

export function useIsLargeScreen() {
  return useMediaQuery("(min-width: 1000px)");
}
